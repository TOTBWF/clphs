{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module CLPHS.FD
    ( FD
    , FDExpr
    , runFD
    , int
    , (#==)
    , (#/=)
    , (#>=)
    , (#<=)
    , (#>)
    , (#<)
    , allDifferent
    , cmax
    , new
    , news
    , label
    )
where

import Control.Monad.State.Lazy
import Control.Monad.Except
import Control.Monad.Logic
import Control.Monad (unless)
import Control.Applicative (Alternative)

import qualified Data.Map as Map
import Data.Map (Map, (!))

-- Debugging
import Debug.Trace

import qualified CLPHS.FD.Domain as Domain
import CLPHS.FD.Domain (Domain, Bound)

{-
The way clpfd works is that is it maintains a queue of propagators, adding them

First, clpfd needs to parse the "Term language" into a series of constraints/propagators.

Also, you shouldn't queue up constraints on the variables, but rather build a propagator tree of some sort?
This makes it easier to remove propagators entirely.
-}

newtype FD s a = FD { unFD :: StateT (FDState s) Logic a }
    deriving (Functor, Applicative, Monad, Alternative, MonadPlus, MonadState (FDState s))

newtype FDVar s = FDVar { unFDVar :: Int }
    deriving (Eq, Ord)

type FDPropagator s = FD s ()

data VarInfo s = VarInfo { delayedPropagators :: [FDPropagator s], values :: Domain }

data FDState s = FDState { varSupply :: FDVar s, varMap :: Map (FDVar s) (VarInfo s), runCount :: Int, wasKilled :: Bool }

initState :: FDState s
initState = FDState { varSupply = FDVar 0, varMap = Map.empty, runCount = 0, wasKilled = False }

runFD :: (forall s . FD s a) -> [a]
runFD s = observeAll $ evalStateT (unFD s) initState
newVar :: Domain -> FD s (FDVar s)
newVar d = do
    v <- nextVar
    v `isOneOf` d
    return v
    where
        nextVar :: FD s (FDVar s)
        nextVar = do
            s <- get
            let v = varSupply s
            put s { varSupply = FDVar (unFDVar v + 1) }
            return v

        isOneOf :: FDVar s -> Domain -> FD s ()
        x `isOneOf` d = modify $ \s ->
            let vm = varMap s
                vi = VarInfo {
                    delayedPropagators = [],
                    values = d
                }
            in s { varMap = Map.insert x vi vm }

rangeVar :: Bound -> Bound -> FD s (FDVar s)
rangeVar l u = newVar $ (Domain.range l u)

unboundedVar :: FD s (FDVar s)
unboundedVar = newVar $ Domain.range Domain.inf Domain.sup

domain :: FDVar s -> FD s Domain
domain x = do
    s <- get
    return $ values $ varMap s ! x

domain' :: FDVar s -> FD s (Domain, Bound, Bound)
domain' x = do
    dx <- domain x
    return (dx, Domain.findMin dx, Domain.findMax dx)

domainBounds :: Domain -> (Bound, Bound)
domainBounds dx = (Domain.findMin dx, Domain.findMax dx)

-- Every propagator trigger should return a list of propagators that should be triggered the next time
trigger :: [FDPropagator s] -> FD s [FDPropagator s]
trigger [] = return []
trigger (p:ps) = do
    p
    k <- gets wasKilled
    revive
    if k then trigger ps else (p:) <$> trigger ps
    -- (p:) <$> trigger ps

triggerPropagators :: [FDPropagator s] -> Domain -> Domain -> FD s [FDPropagator s]
triggerPropagators ps d d'
    | d /= d' = trigger ps
    | otherwise = return ps
    -- when (d /= d') $ trigger ps

getVarInfo :: FDVar s -> FD s (VarInfo s)
getVarInfo x = gets ((! x)  . varMap)

updateVarInfo :: FDVar s -> VarInfo s -> FD s ()
updateVarInfo x vi = modify (\s -> s { varMap = Map.insert x vi (varMap s) })

update :: FDVar s -> Domain -> FD s ()
update x d = do
    vi <- getVarInfo x
    updateVarInfo x (vi { values = d })
    ps' <- triggerPropagators (delayedPropagators vi) (values vi) d
    updateVarInfo x (vi { values = d, delayedPropagators = ps' })

addConstraint :: FDVar s -> FDPropagator s -> FD s ()
addConstraint x propagator = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    let cs = delayedPropagators vi
    put $ s { varMap = Map.insert x (vi { delayedPropagators = propagator:cs }) vm }

type BinaryPropagator s = FDVar s -> FDVar s -> FDPropagator s

addBinaryPropagator :: BinaryPropagator s -> BinaryPropagator s
addBinaryPropagator f x y = do
    let constraint = f x y
    constraint
    addConstraint x constraint
    addConstraint y constraint

-- kill should prevent a propagator from being run again, 
-- as all of the values have been constrainted in such a way that it will always be true
kill :: FD s ()
kill = modify (\s -> s { wasKilled = True }) 

revive :: FD s ()
revive = modify (\s -> s { wasKilled = False }) 

hasValue :: FDVar s -> Int -> FDPropagator s
x `hasValue` n = do
    dx <- domain x
    guard $ n `Domain.member` dx
    let d = Domain.singleton n
    update x d

-- | Attempts to solve a series of expressions
varsLabel :: [FDVar s] -> FD s [Int]
varsLabel = mapM label
    where
        label var = do
            vals <- domain var
            val <- FD . lift $ msum $ return <$> Domain.toList vals
            var `hasValue` val
            return val
        

{-
When we are presented with a CLP expression, we need to interpret it as a series
of constraints and propagators that need to be triggered once.
-}

data FDExpr s
    = Int !Int
    | Var !(FDVar s)
    | !(FDExpr s) :+ !(FDExpr s)
    | !(FDExpr s) :- !(FDExpr s)
    -- | Times !(FDExpr s) !(FDExpr s)
    | Max !(FDExpr s) !(FDExpr s)

instance Num (FDExpr s) where
    (+) = (:+)
    (-) = (:-)
    -- (*) = Times
    fromInteger = Int . fromInteger

int :: Int -> FDExpr s
int = Int

-- | Takes an FDExpr and generates an auxilary variable representing the result of the expression
interpret :: FDExpr s -> FD s (FDVar s)
interpret (Int n) = newVar $ Domain.singleton n
interpret (Var v) = return v
interpret (x :+ y) = do
    vx <- interpret x
    vy <- interpret y
    vz <- unboundedVar
    pplus vx vy vz
    return vz
interpret (x :- y) = do
    vx <- interpret x
    vy <- interpret y
    vz <- unboundedVar
    pplus vy vz vx
    return vz
interpret (Max x y) = do
    vx <- interpret x
    vy <- interpret y
    vz <- unboundedVar
    vz `pgeq` vx
    vz `pgeq` vy
    pmax vx vy vz
    return vz

{-
Propagators
-}
peq :: FDVar s -> FDVar s -> FDPropagator s
peq = addBinaryPropagator $ \x y -> do
    dx <- domain x
    dy <- domain y
    let i = Domain.intersection dx dy
    guard $ not $ Domain.null i
    update x i
    update y i

pneq :: FDVar s -> FDVar s -> FDPropagator s
pneq = addBinaryPropagator $ \x y -> do
    -- modify(\s@FDState { runCount = c } -> trace ("Run Count:" ++ show (c + 1)) (s { runCount = c + 1 }))
    dx <- domain x
    dy <- domain y
    case (Domain.isSingleton dx, Domain.isSingleton dy) of
        (Just vx, Just vy) -> guard (vx /= vy) >> kill
        (Just vx, Nothing) -> putDomain y dy (Domain.remove vx dy)
        (Nothing, Just vy) -> putDomain x dx (Domain.remove vy dx)
        (Nothing, Nothing) -> do
            let (dxl, dxu) = domainBounds dx
            let (dyl, dyu) = domainBounds dy
            when (dxu < dyl) $ kill
            when (dxl > dyu) $ kill

pgeq :: FDVar s -> FDVar s -> FDPropagator s
pgeq = addBinaryPropagator $ \x y -> do
    dx <- domain x
    dy <- domain y
    case (Domain.isSingleton dx, Domain.isSingleton dy) of
        (Just vx, Just vy) -> guard (vx >= vy) >> kill
        (Just vx, Nothing) -> do
            let dy' = Domain.removeGreater (fromIntegral vx) dy
            update y dy'
            kill
        (Nothing, Just vy) -> do
            let dx' = Domain.removeLesser (fromIntegral vy) dx
            update x dx'
            kill
        (Nothing, Nothing) -> do
            let (dxl, dxu) = domainBounds dx
            let (dyl, dyu) = domainBounds dy
            guard $ (dxu >= dyl)


    -- unless (Domain.findMin dx >= Domain.findMax dy) $ pgeq x y
    -- where
    --     pgeq :: FDVar s -> FDVar s -> FDPropagator s
    --     pgeq x y = do
    --         (dx, dxl, dxu) <- domain' x
    --         (dy, dyl, dyu) <- domain' y
    --         unless (dxl >= dyu) $ do
    --             updateBounds x (max dxl dyl) dxu 
    --             updateBounds y dyl (min dxu dyu)

pplus :: FDVar s -> FDVar s -> FDVar s -> FDPropagator s
pplus x y z = do
    (dx, dxl, dxu) <- domain' x
    (dy, dyl, dyu) <- domain' y
    (dz, dzl, dzu) <- domain' z
    let dxl' = max dxl (dzl - dyu)
    let dxu' = min dxu (dzu - dyl)
    updateBounds x dxl' dxu'
    (dy, dyl, dyu) <- domain' y
    let dyl' = max dyl (dzl - dxu')
    let dyu' = min dyu (dzu - dxl')
    updateBounds y dyl' dyu'
    (dz, dzl, dzu) <- domain' z
    let dzl' = max dzl (dxl' + dyl')
    let dzu' = min dzu (dxu' + dyu')
    updateBounds z dzl' dzu'

pmax :: FDVar s -> FDVar s -> FDVar s -> FDPropagator s
pmax x y z = do
    dz <- domain z
    (_, dxl, dxu) <- domain' x
    (_, dyl, dyu) <- domain' y
    if | dyl > dxu -> peq z y
       | dyu < dxl -> peq z x
       | otherwise -> do
            let dz' = Domain.removeGreater (max dxu dyu) dz
            putDomain z dz dz'

ptimes :: FDVar s -> FDVar s -> FDVar s -> FDPropagator s
ptimes x y z = do
    dx <- domain x
    dy <- domain y
    dz <- domain z
    (dxl', dxu') <- factor dx dy dz
    updateBounds x dxl' dxu'
    return undefined
    where 
        factor :: Domain -> Domain -> Domain -> FD s (Bound, Bound)
        factor dx dy dz = 
            let (dxl, dxu) = domainBounds dx
                (dyl, dyu) = domainBounds dy
                (dzl, dzu) = domainBounds dz
            in if | dxu < 0 && dyl < 0 && dyu > 0 && dzl < 0 && dzu > 0 -> do
                        z1 <- rangeVar dxl dxu--newVar (Domain.range dxl dxu)
                        z2 <- rangeVar dxl dxu
                        x1 <- rangeVar dyl (-1)
                        y1 <- rangeVar 1 dzu
                        undefined




updateBounds :: FDVar s -> Bound -> Bound -> FDPropagator s
updateBounds x dxl' dxu' = do
    (dx, dxl, dxu) <- domain' x
    unless (dxl == dxl' && dxu == dxu') $ do
        let dx' = Domain.intersection dx (Domain.range dxl' dxu')
        putDomain x dx dx'

putDomain :: FDVar s -> Domain -> Domain -> FDPropagator s
putDomain x dx dx' = do
    guard $ not $ Domain.null dx'
    when (dx' /= dx) $ update x dx'


liftJ2 :: (Monad m) => (a -> b -> m c) -> m a -> m b -> m c
liftJ2 f x y = join $ liftM2 f x y

liftJ3 :: (Monad m) => (a -> b -> c -> m d) -> m a -> m b -> m c -> m d
liftJ3 f x y z = join $ liftM3 f x y z

infixl 1 #==, #/=, #<=, #>=, #>, #<

-- TODO: Implement a simplifier for certain constraints, we could save a ton of work here.
-- Auxillary variables are super expensive, so we should avoid them whenever possible

(#==) :: FDExpr s -> FDExpr s -> FDPropagator s
x #== (y :+ z) = liftJ3 pplus (interpret x) (interpret y) (interpret z)
x #== (y :- z) = liftJ3 pplus (interpret x) (interpret z) (interpret y)
x #== y = liftJ2 peq (interpret x) (interpret y)

(#/=) :: FDExpr s -> FDExpr s -> FDPropagator s
x #/= y = liftJ2 pneq (interpret x) (interpret y)

(#>=) :: FDExpr s -> FDExpr s -> FDPropagator s
x #>= y = liftJ2 pgeq (interpret x) (interpret y)

(#<=) :: FDExpr s -> FDExpr s -> FDPropagator s
x #<= y = y #>= x

(#>) :: FDExpr s -> FDExpr s -> FDPropagator s
x #> y = (x + 1) #>= y

(#<) :: FDExpr s -> FDExpr s -> FDPropagator s
x #< y = y #> x

allDifferent :: [FDExpr s] -> FDPropagator s
allDifferent (x:xs) = do
    mapM_ (#/= x) xs
    allDifferent xs
allDifferent [] = return ()

cmax :: [FDExpr s] -> FDExpr s
cmax = foldl1 Max


new :: Domain -> FD s (FDExpr s)
new d = Var <$> newVar d

news :: Int -> Domain -> FD s [FDExpr s]
news n d = replicateM n (new d)

label :: [FDExpr s] -> FD s [Int]
label = varsLabel <=< mapM interpret