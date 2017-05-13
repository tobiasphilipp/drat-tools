{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}


module Main where

import System.Environment (getArgs)
import qualified Data.ByteString.Char8 as B

import Data.CNF
import Data.DRAT
import Data.Parse.DimacsCNF
import Data.Parse.DRAT
import Control.Monad.ST
import Control.Monad.Primitive
import Control.Monad.State
import Control.Monad
import Control.Monad.Reader
import Control.Arrow (first, second)


import Prelude hiding (lookup, length)


import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as M
import Data.Word

import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Linear as HB

import Data.Maybe (fromJust, isJust, catMaybes)

import Data.List (take, drop, partition, sort)

import Debug.Trace (traceM)
import Data.Primitive.MutVar
import System.IO.Unsafe (unsafePerformIO)

traceD x = return ()
--traceD x = traceM x

traceW x = traceD $ "w: " ++ x -- Trace TwoWatcher Operations
traceI x = traceD $ "i: " ++ x
traceP x = traceD $ "p: " ++ x
traceA x = traceD $ "a: " ++ x
traceS x = traceD $ "s: " ++ x


-- *  Clause storage




-- | A ClauseStorage assigns a unique id to each clause.
-- At the beginning all clauses that occur in the formula or the proof are put into the clause storage.
-- This allows to reference them using only their ids.
data ClauseEntry = ClauseEntry { cwatches :: {-# UNPACK #-} !(Literal, Literal)
                               , clause :: Clause
                               }
                               deriving (Eq, Show)

satStatus :: Word8
{-# INLINE satStatus #-}
satStatus = 1

unsatStatus :: Word8
{-# INLINE unsatStatus #-}
unsatStatus = 0


newtype ClauseStorage s = ClauseStorage { cclauses :: VM.MVector s ClauseEntry -- ^Each position in the vector contains a clause.
                                        }

phantomLiteral :: Literal
{-# INLINE phantomLiteral #-}
phantomLiteral = 0

fromListAndTranslateProof :: (PrimMonad m) => DimacsCNF -> ProofSequence -> m (IndexedProofSequence, ClauseStorage (PrimState m))
fromListAndTranslateProof (DimacsCNF nv nc f) (ProofSequence ncp p) = do
  let (addedC, delC) = partition (\(o,x) -> o == ADD) p
      allC = map sort $ f ++ map snd addedC

  cs <- fromList allC

  ht <- liftPrim $ HB.newSized (nc + ncp)
  liftPrim $ mapM_ (uncurry (H.insert ht)) (zip allC [0..])

  (_, p') <- liftPrim $ foldM (go ht) (nc, []) p
  return (IndexedProofSequence ncp (reverse p'), cs)
  where
    go _ (!i, xs) (ADD, cl) = return (i+1, (ADD, i, sort cl):xs)
    go ht (!i, xs) op@(DEL, cl) = do
      let cl' = sort cl
      iD <- H.lookup ht cl'
      case iD of
        (Just x) -> return (i, (DEL, x, cl'):xs)
        Nothing -> do
          traceM $ "Ignoring Deletion of non existing clause.." ++ show op
          return (i, xs)

lengthCS :: (PrimMonad m) => ClauseStorage (PrimState m) -> m Int
lengthCS = return . VM.length . cclauses

-- | assigns watches for non unit clauses
fromList :: (PrimMonad m) => [Clause] -> m (ClauseStorage (PrimState m))
fromList cls = do
  let cls' = map go cls
      v = V.fromList cls'
  vm <- V.unsafeThaw v
  return (ClauseStorage vm)

  where
    go :: Clause -> ClauseEntry
    go [] = error "emptry clause!"
    go cl@(x:y:xs) = ClauseEntry { cwatches = (x, y), clause = cl }
    go cl@(x:xs) = ClauseEntry   { cwatches = (phantomLiteral, phantomLiteral), clause = cl}



toListCS :: (PrimMonad m) => ClauseStorage (PrimState m) -> m [ClauseEntry]
toListCS storage = V.toList <$> V.freeze (cclauses storage)

toListWithId :: (PrimMonad m) => ClauseStorage (PrimState m) -> m [(ClauseId, ClauseEntry)]
toListWithId storage = zip [0..] <$> toListCS storage

toListUpTo :: (PrimMonad m) => Int -> ClauseStorage (PrimState m) -> m [(ClauseId, ClauseEntry)]
toListUpTo n storage = zip [0..n-1] <$> toListCS storage



lookupEntry :: (PrimMonad m) => ClauseId -> ClauseStorage (PrimState m) -> m ClauseEntry
--{-# INLINE lookupEntry #-}
lookupEntry i storage = VM.unsafeRead (cclauses storage) i

writeEntry :: (PrimMonad m) => ClauseId -> ClauseStorage (PrimState m) -> ClauseEntry -> m ()
--{-# INLINE writeEntry #-}
writeEntry cid storage entry = VM.unsafeWrite (cclauses storage) cid entry


modifyEntry :: (PrimMonad m) => ClauseId -> ClauseStorage (PrimState m) -> (ClauseEntry -> ClauseEntry) -> m ()
--{-# INLINE modifyEntry #-}
modifyEntry cid storage f = VM.unsafeModify (cclauses storage) f cid

-- * Assignment
-- Based on mutable vectors. Each Literal can either be true, false, or unassigned in a given assignment.


-- | An assignment is represented by a mutable vector.
-- TODO: @wko: replace int by own datastructure that can also be boxed.
type LiteralStatus = Word8


-- | The 'literalToIndex' function computes an index [0..] for a
-- literal [..., n, -n, n+1, -(n+1), ...]
literalToIndex :: Literal -> Int
{-# INLINE literalToIndex #-}
literalToIndex lit | lit > 0   = 2*lit
                   | otherwise = (-2)*lit+1


trueConst :: LiteralStatus
{-# INLINE trueConst #-}
trueConst = 2

falseConst :: LiteralStatus
{-# INLINE falseConst #-}
falseConst = 1

unassignedConst :: LiteralStatus
{-# INLINE unassignedConst #-}
unassignedConst = 0

type Assignment s = M.MVector s LiteralStatus





initialAssignment :: (PrimMonad m)
                  => Int -- ^number of atoms
                  -> m (Assignment (PrimState m))
initialAssignment n = M.replicate (2*(n+1)) unassignedConst

assignmentFromList :: (PrimMonad m)
                   => Int -- ^number of atoms
                   -> [Literal] -- ^list of true literals
                   -> m (Assignment (PrimState m))
assignmentFromList n ls =
  do
    ass <- initialAssignment n
    Control.Monad.forM_ ls $
      \lit -> makeTrue ass lit
    return ass

assignmentToList :: (PrimMonad m) => Assignment (PrimState m) -> m [Int]
assignmentToList z =
  do
    let len = M.length z
    iv <- Control.Monad.filterM (isNotUnknown z) [1..(len `div` 2) - 1]
    Prelude.mapM (ff z) iv
  where
    ff ass lit =
      do
        it <- isTrue ass lit
        if it then return lit else return $ (-1) * lit

    isNotUnknown z lit =
      do
        v <- M.read z (literalToIndex lit)
        return (v /= unassignedConst)

makeAssignmentHelper :: (PrimMonad m)
                     => Assignment (PrimState m) -- ^the mutable assignment vector
                     -> Literal                     -- ^the literal
                     -> LiteralStatus                         -- ^value for the positive literal
                     -> LiteralStatus                         -- ^value for the negated literal
                     -> m ()
{-# INLINE makeAssignmentHelper #-}
makeAssignmentHelper vec lit val1 val2 =
  do
      M.unsafeWrite vec (literalToIndex lit) val1
      M.unsafeWrite vec (literalToIndex (-lit)) val2
      return ()

makeUnknown :: (PrimMonad m) => Assignment (PrimState m)  -> Literal -> m ()
{-# INLINE makeUnknown #-}
makeUnknown vec lit = makeAssignmentHelper vec lit unassignedConst unassignedConst

makeTrue :: (PrimMonad m) => Assignment (PrimState m)  -> Literal -> m ()
{-# INLINE makeTrue #-}
makeTrue vec lit = makeAssignmentHelper vec lit trueConst falseConst

makeFalse :: (PrimMonad m) => Assignment (PrimState m)  -> Literal -> m ()
{-# INLINE makeFalse #-}
makeFalse vec lit = makeTrue vec (-lit)


isVal :: (PrimMonad m)
      => Assignment (PrimState m)
      -> Literal
      -> (Word8 -> Bool) -- Comparison function
      -> m Bool
{-# INLINE isVal #-}
isVal vec lit cmp = fmap cmp $! M.unsafeRead vec $! literalToIndex lit

isTrue :: (PrimMonad m) => Assignment (PrimState m) -> Literal -> m Bool
{-# INLINE isTrue #-}
isTrue vec lit =  isVal vec lit (== trueConst)

isFalse :: (PrimMonad m) => Assignment (PrimState m) ->  Literal -> m Bool
{-# INLINE isFalse #-}
isFalse vec lit = isVal vec lit (== falseConst)

isUnknown :: (PrimMonad m) => Assignment (PrimState m) ->  Literal -> m Bool
{-# INLINE isUnknown #-}
isUnknown vec lit = isVal vec lit (== unassignedConst)

isNotFalse :: (PrimMonad m) => Assignment (PrimState m) ->  Literal -> m Bool
{-# INLINE isNotFalse #-}
isNotFalse vec lit = isVal vec lit (/= falseConst)

isNotTrue :: (PrimMonad m) => Assignment (PrimState m) ->  Literal -> m Bool
{-# INLINE isNotTrue #-}
isNotTrue vec lit = isVal vec lit (/= trueConst)

makeUnknownTrue vec lit =
  do
    val <- isUnknown vec lit
    when val $ makeTrue vec lit





-- * Two Watcher

-- | Mapping from Literals to an IntMap representing a mapping from clauseIds to the other watched literal in the clause.
-- The watches mapping is allowed to contain clause ids that are not really watched anymore.


-- | Add two watches for a clauseid.
-- $O(1)$
addWatch :: (PrimMonad m) => (Literal, Literal) -> ClauseId -> TwoWatcher (PrimState m) -> m ()
addWatch (l1, l2) i w = do
  traceW $ "adding watch for literal " ++ show l1 ++  " in Clause " ++ show i
  VM.modify w (i:) (literalToIndex l1)
  traceW $ "adding watch for literal " ++ show l2 ++  " in Clause " ++ show i
  VM.modify w (i:) (literalToIndex l2)

-- | Delete two watches for a clauseid.
-- The watches are deleted only in clWatches. Therefore this function leaves old invalid entries in watches.
-- The invalid entries can later be filtered out by the function 'getRealWatches'.
-- $O(1)$
deleteWatch :: (PrimMonad m) => (Literal, Literal) -> ClauseId -> ClauseStorage (PrimState m) -> m ()
deleteWatch _ i storage = modifyEntry i storage (\x -> x { cwatches = (0, 0)})


-- | Delete two watches for a clauseid.
-- The watches are deleted only in clWatches. Therefore this function leaves old invalid entries in watches.
-- The invalid entries can later be filtered out by the function 'getRealWatches'.
-- $O(n+m)$ where $n, m$ are the length of the watch lists respectively.
deleteWatchStrict :: (PrimMonad m) => (Literal, Literal) -> ClauseId -> AppState (PrimState m) -> m ()
deleteWatchStrict l@(l1, l2) i state = do
  deleteWatch l i (clauseS state)
  VM.modify (watcher state) (L.delete i) (literalToIndex l1)
  VM.modify (watcher state) (L.delete i) (literalToIndex l2)


-- | Delete the current watches of a clauseid. Note that only clWatches is updated.
-- $O(1)$
deleteWatchByClauseId :: (PrimMonad m) => ClauseId -> ClauseStorage (PrimState m) -> m ()
deleteWatchByClauseId cid storage = modifyEntry cid storage (\x -> x { cwatches = (0, 0) })

-- | Updates the watch of a clauseid.
updateWatch :: (PrimMonad m)
          => (Literal, Literal) -- ^Old watches
          -> (Literal, Literal)    -- ^New watched literals
          -> ClauseId
          -> TwoWatcher (PrimState m)
          -> m ()
updateWatch (l1_old, l2_old) ln@(l1_new, l2_new) i w = do
  let l_new = (L.filter (not . (`elem` [l1_old, l2_old])) [l1_new, l2_new])
      l_old = (L.filter (not . (`elem` [l1_new, l2_new])) [l1_old, l2_old])

  traceP $ "updating watch:" ++ show i ++ " clid, with lit" ++ show l_new

  if L.length l_new > 1 then
    traceP $ "more than one watch changed at the same time!!"
  else
    traceP ""
  mapM_ (VM.modify w (i:) . literalToIndex) l_new
  -- VM.unsafeWrite (clWatches w) i (Just ln)


-- | Updates the watch of a clauseid and remove the invalid entry in 'watches'.
updateWatchStrict :: (PrimMonad m)
                  => (Literal, Literal) -- ^Old watches
                  -> (Literal, Literal)    -- ^New watched literals
                  -> ClauseId
                  -> TwoWatcher (PrimState m)
                  -> m ()
updateWatchStrict (l1_old, l2_old) ln@(l1_new, l2_new) i w = do
  let l_new = (L.filter (not . (`elem` [l1_old, l2_old])) [l1_new, l2_new])
      l_old = (L.filter (not . (`elem` [l1_new, l2_new])) [l1_old, l2_old])

  traceP $ "updating watch:" ++ show i ++ " clid, with lit" ++ show l_new

  if L.length l_new > 1 then
    traceP $ "more than one watch changed at the same time!!"
  else
    traceP ""
  mapM_ (VM.unsafeModify w (L.delete i) . literalToIndex) l_old
  mapM_ (VM.unsafeModify w (i:) . literalToIndex) l_new
  -- VM.unsafeWrite (clWatches w) i (Just ln)


-- |Return the clauseids of clauses in which a given literal is watched.
getWatches :: (PrimMonad m) => TwoWatcher (PrimState m) -> Literal -> m [ClauseId]
{-# INLINE getWatches #-}
getWatches w l = VM.unsafeRead w (literalToIndex l)

-- |Return the clauseids of clauses in which a given literal is watched.
-- Additionally filters clauseIds in which the literal is not watched anymore.
getRealWatches :: (PrimMonad m) => AppState (PrimState m) -> Literal -> m [ClauseId]
getRealWatches w l = do
  cls <- getWatches (watcher w) l
  cls' <- foldM (go (clauseS w) l) [] cls
  VM.unsafeWrite (watcher w) (literalToIndex l) cls'
  return cls'

  where
    go :: PrimMonad m
       => ClauseStorage (PrimState m)
       -> Literal -- ^Literal that is being watched
       -> [ClauseId] -- ^Accumulator containing really watched clauses
       -> ClauseId -- ^Clause that is to be checked
       -> m [ClauseId] -- ^The modified accumulator
    go storage l cls cl = do
      r <- cwatches <$> lookupEntry cl storage
      case r of
        (0, 0) -> return cls
        (l1, l2) -> if (l == l1 || l == l2) then return (cl:cls)
                      else return cls

-- |The two watches of a clauseid using the clWatches mapping.
-- $O(1)$
getClauseWatches :: (PrimMonad m) => AppState (PrimState m) -> ClauseId -> m (Literal, Literal)
getClauseWatches st i = cwatches <$> lookupEntry i (clauseS st)


-- | Initialize a TwoWatcher
initializeWatcher :: (PrimMonad m)
                => Int -- ^ Number of Variables
                -> Int -- ^ Total Number of Clauses
                -> m (TwoWatcher (PrimState m))
initializeWatcher numvars numClauses = VM.replicate ((numvars+1)*2) []



-- | Sets up watches for each clause in the clause storage that is currently active.
-- Active here means that clauses that are going to be added in the future proof checking steps are not active yet.
setupWatchesForClauseStorage :: (PrimMonad m)
                             => AppState (PrimState m)
                             -> Int
                             -> m ()
setupWatchesForClauseStorage state n = do
   mapM_ (setupWatchForClause state) [0..n]
  where
    setupWatchForClause :: (PrimMonad m) => AppState (PrimState m) -> ClauseId -> m ()
    setupWatchForClause state cid = do
      entry <- lookupEntry cid (clauseS state)
      case cwatches entry of
        (0, 0) -> traceS "Setting up watches for unit clause does not work"
        lits -> addWatch lits cid (watcher state)


-- * Unit propagation functions

-- | The main data type of the AppState
data AppState s = AppState { clauseS      :: ClauseStorage s -- ^ the mapping from ids to clauses
                           , watcher      :: VM.MVector s [ClauseId] -- ^ stores for each literal a list ids of watched clauses
                           , assignment   :: Assignment s -- ^ the current (partial) assignment
                           , propagationQueue :: MutVar s [Literal] -- ^ the propagation queue containing a list of literals that are to be propagated initially.
                           }
type TwoWatcher s = VM.MVector s [ClauseId]


type PropagationUnits = [Literal]
data PropagationResult = EmptyClauseFound | NoUnitLeft | None
  deriving (Eq, Show)


-- | Run unit propagation until no unit clauses can be found anymore or a conflict was found. Returns a list of propagation units
-- so that the changes can later be undone.
exhaustiveUnitPropagation :: PrimMonad m
                          => AppState (PrimState m)
                          -> [Literal]
                          -> m (PropagationResult, PropagationUnits)
exhaustiveUnitPropagation fw q = do
  traceP "exhaustiveUnitPropagation"
  -- TODO: What happens if Formula contains empty clause already?
  --t <- containsEmptyClause fw
  --if t then do
  --  traceP $ "Formula contains empty clause already, no need for further unit propagation"
  --  return (EmptyClauseFound, [])
  --  else do
  (r, pu) <- propagate fw q
  case r of
    EmptyClauseFound -> traceP "Found Empty Clause" >> return (EmptyClauseFound, pu)
    _ -> traceP "No Empty Clause found.." >> return (r, pu)

-- | Undo the modifications introduced by running unit propagation. Unassigns the unit literals and resets the clause status vector.
undoModifications :: PrimMonad m => [Literal] -> AppState (PrimState m) -> m ()
undoModifications pr state = do
  undoAssignmentModifications (assignment state) pr
  -- Reset satisfied clauses
  --mapM_ (\cid -> modifyEntry cid (clauseS state) (\cl -> cl { cstatus = unsatStatus })) cids





  --setupWatchesForClauseStorage cls (watcher fw) -- reset watches TODO: This could be done more efficiently I think
initialize :: (PrimMonad m) => DimacsCNF -> ProofSequence -> m (AppState (PrimState m), PropagationResult, PropagationUnits, IndexedProofSequence)
initialize = initialStateWithPropagation

-- | Insert a new clause, identified by its clause id, into the twoWatcher.
insert :: PrimMonad m => ClauseId -> AppState (PrimState m) -> m ()
insert clid fw = do
  -- TODO: What happens if we insert the empty clause?
  cl <- lookupEntry clid (clauseS fw)
  traceI $ "Inserting " ++ show cl
  r <- analyzeC (assignment fw) (clause cl)
  -- TODO: @wko: maybe overwrite the reduced version in the clause storage?
  traceI $ "Reduced version " ++ show r
  case r of
    ARUnit l -> do
      -- add Clause to propagationQueue
      -- makeTrue (assignment fw) l
      traceI $ "Adding to propagation queue: " ++ show l
      modifyMutVar' (propagationQueue fw) (l:)
    AROther l1 l2 -> do
      -- add Watches
      addWatch (l1, l2) clid (watcher fw)
    _ -> return ()

-- | Remove a clause, identified by its id, from the twoWatcher by removing its watches.
remove :: PrimMonad m => ClauseId -> AppState (PrimState m) -> m ()
remove clid fw = do
      -- removeWatches
      deleteWatchByClauseId clid (clauseS fw)

toListFW :: (PrimMonad m) => AppState (PrimState m) -> m [Clause]
toListFW fw = do             -- TODO: Use sat information here for better performance
  cls <- toListCS (clauseS fw)
  catMaybes <$> mapM (reduce (assignment fw) . clause) cls

clausesContainingLiteral :: (PrimMonad m) => Literal -> AppState (PrimState m) -> m [Clause]
clausesContainingLiteral l fw = filter (l `elem`) <$> toListFW fw





-- | Representation of the result of analyzing a clause.
data ARResult = ARConflict |  ARUnit {-# UNPACK #-} !Literal | AROther {-# UNPACK #-} !Literal !Literal | ARSat
  deriving (Show, Eq)

arToMaybe :: ARResult -> Maybe Literal
{-# INLINE arToMaybe #-}
arToMaybe (ARUnit i)  = Just i
arToMaybe _ = Nothing



-- |Analyze a clause under given partial assignment.
-- If the clause is not satisfied yet and >= 2 literals in the clause are unassigned,
-- The clause analysis is stopped.
analyzeC :: (PrimMonad m)
         => Assignment (PrimState m)  -- ^partial assignment vector
         -> Clause
         -> m ARResult
--{-# INLINE analyzeC #-}
analyzeC z c =  analyzeCh z c 0 0 0
  where
    -- | Analyze a clause under given partial assignment
    analyzeCh :: (PrimMonad m)
              => Assignment (PrimState m)    -- ^partial assignment vector
              -> Clause                      -- ^clause to analyze
              -> Int                         -- ^ count of unassigned literals in clause
              -> Int                         -- ^ used to store unassigned literals
              -> Int
              -> m ARResult
    {-# INLINE analyzeCh #-}
    analyzeCh _ [] 0 _ _ = return ARConflict
    analyzeCh z [] 1 !u _ = return $! ARUnit u
    analyzeCh _ _ 2 !u !w = return $! AROther u w
    analyzeCh z (l:ls) 0 !u !w = do
      litVal <- M.unsafeRead z  (literalToIndex l)
      case litVal of
       2 -> return ARSat            -- Clause is satisfied
       1 -> analyzeCh z ls 0 u w         -- current literal is false
       0 -> analyzeCh z ls 1 l w      --
    analyzeCh z (l:ls) 1 !u !w = do
      litVal <- M.unsafeRead z  (literalToIndex l)
      case litVal of
       2 -> return ARSat            -- Clause is satisfied
       1 -> analyzeCh z ls 1 u w         -- current literal is false
       0 -> return $! AROther u l



-- | Returns Nothing if the clause is satisfied
reduce :: (PrimMonad m)
       => Assignment (PrimState m) -- ^ Assignment
       -> Clause
       -> m (Maybe Clause)
{-# INLINE reduce #-}
reduce _ [] = return (Just [])
reduce z cl = foldM (go z) (Just []) cl
  where
    go :: (PrimMonad m)
       => Assignment (PrimState m)
       -> Maybe Clause -> Literal -> m (Maybe Clause)
    go _ Nothing _ = return Nothing
    go z cl@(Just lits) l = do
      sat <- isTrue z l
      if sat then return Nothing
        else do
          unsat <- isFalse z l
          if unsat then return cl
            else return (Just (l:lits))

-- |Check if a given clause is unit given an assignment
isUnit :: (PrimMonad m) => Assignment (PrimState m) -> Clause -> m (Maybe Int)
isUnit z c = do
  aR <- analyzeC z c
  case aR of
   (ARUnit u) -> return $! Just u
   _ -> return Nothing



-- |Check if a given clause is empty given an assignment
isEmptyClause :: (PrimMonad m)
              => Assignment (PrimState m) -- ^ Assignment
              -> Clause
              -> m Bool
isEmptyClause z c = do
  aR <- analyzeC z c
  case aR of
   ARConflict -> return True
   _ -> return False


-- |Assigns Literal to true, if literal is not false already. Return True if a conflict was found.
setTrueExitOnConflictL :: (PrimMonad m)
                       => Assignment (PrimState m)
                       -> Literal
                       -> m Bool
setTrueExitOnConflictL ass l = do
  conflictFound <- isFalse ass l
  if conflictFound then return True
    else do
      makeTrue ass l
      return False

-- | Assigns Literals to true, if literals are not false already. Return if a conflict was found and all the
-- literals that were set to true.
setTrueExitOnConflict :: (PrimMonad m)
                      => Assignment (PrimState m)
                      -> [Literal]
                      -> m (Bool, [Literal])
setTrueExitOnConflict ass =
  foldM ( \(c, ls) l -> do
    if c then return (c, ls) else do
      gotConflict <- setTrueExitOnConflictL ass l
      if gotConflict then return (True, ls)
        else return (False, l:ls)) (False, [])



-- | Returns False if a contradiction was found, True otherwise
propagate :: (PrimMonad m)
          => AppState (PrimState m)
          -> [Literal]
          -> m (PropagationResult, PropagationUnits)
propagate w q = do
  -- get entries from propagation queue and set them to true/ check for conflict
  q' <- readMutVar (propagationQueue w)
  writeMutVar (propagationQueue w) []

  let queue = q ++ q'
  --traceM $ show q' ++ " - " ++ show q

  (gotConflict, lits) <- setTrueExitOnConflict (assignment w) queue
  if gotConflict then
    return (EmptyClauseFound, lits)
  else propagateH w (q++q') lits


propagateH :: (PrimMonad m)
           => AppState (PrimState m)
           -> [Literal]                               -- ^Propagation Queue
           -> [Literal]                               -- ^Assigned Literals
           -> m (PropagationResult, PropagationUnits)
propagateH state [] implied = do
  traceTwoWatcher state
  return (NoUnitLeft, implied)
propagateH state (lit:ls) implied =
  do
    traceTwoWatcher state
    let z = assignment state
    --zl <- assignmentToList z
    --traceA $ "cs: current assignment:" ++ show zl

    traceP $ "p: propagationQueue " ++ show (lit:ls)
    traceP $ "p: propagate " ++ show lit
    tv <- M.unsafeRead z (literalToIndex lit)
    case tv of
      --2 -> do
      --  traceP "no need to propagate, since literal is already true "
      --  propagateH w ls implied -- Literal is already true
      1 -> do
        --traceP "This should not happen"
        traceP "p: cannot propagate, since it is already false "
        return (EmptyClauseFound, implied)
      _ ->
        do
          traceP $  "p: assign literal to true " ++ show lit
          makeTrue z lit
          relevantClauseIds <- getRealWatches state (-lit)
          traceP $ "relevant clauses:" ++ show relevantClauseIds
          (gotConflict, impliedLiterals) <- foldM (go state) (False, []) relevantClauseIds

          --mapM_ (makeTrue z) impliedLiterals
          let implied' = lit:impliedLiterals ++ implied


          case gotConflict of
            False -> do
              traceP $ "p: implied literals = " ++ show impliedLiterals
              -- Directly adding impliedLiterals to the assignment reduces calls on processClause
              conflict <- or <$> mapM (isFalse z) impliedLiterals
              if conflict then do
                traceP "p: cannot propagate, since it is already false "
                return (EmptyClauseFound, implied')
              else
                do
                  propagateH state (impliedLiterals ++ ls) implied'
            True -> do
              traceP "p: one clause got empty"
              traceTwoWatcher state
              return (EmptyClauseFound, implied')
  where
    go :: (PrimMonad m)
       => AppState (PrimState m)
       -> (Bool, [Literal])
       -> ClauseId
       -> m (Bool, [Literal])
    go w (False, xs) c = do
      r <- processClause c w
      case r of
        ARConflict -> return (True, xs)
        (ARUnit l) -> do
          ---------------------------------------------------------
          -- directly add newly found literal to assignment for fewer calls to processClause and updateWatch
          makeTrue (assignment w) l
          ---------------------------------------------------------
          return (False, l:xs)
        ARSat -> return (False, xs)
        (AROther _ _) -> return (False, xs)
    go _ x _ = return x -- conflict found



-- | analyzes clause under current assignment, collects unit or updates watches
processClause :: (PrimMonad m) => ClauseId -> AppState (PrimState m) -> m ARResult
processClause i st = do
  entry@(ClauseEntry lcur cl) <- lookupEntry i (clauseS st)

  r' <- analyzeC (assignment st) cl
  case r' of
    x@(AROther l1new l2new) -> do -- Clause still has at least two literals, update watches
      let lnew = (l1new, l2new)
      updateWatch lcur lnew i (watcher st)
      writeEntry i (clauseS st) (entry { cwatches = lnew })
      return x
    x@ARSat -> do -- Clause is satisfied so remove its watches
      --deleteWatch (l1, l2) i (watcher w)
      -- Add clauseid to satisfied clauses
      traceP $ "Setting clause sat: " ++ show i
      --writeEntry i (clauseS st) (entry { cstatus = satStatus })
      return x
    x -> return x -- clause is unit


-- |Reset the assignment after unit propagation was run
undoAssignmentModifications :: (PrimMonad m)
                  => Assignment (PrimState m)
                  -> [Literal]
                  -> m ()
undoAssignmentModifications z lits = do
  traceA "um: Undoing modifications"
  forM_ lits $ \l -> makeUnknown z l


-- | Creates a FullWatcher for a given formula
initialStateWithPropagation :: (PrimMonad m)
                            => DimacsCNF
                            -> ProofSequence
                            -> m (AppState (PrimState m), PropagationResult, PropagationUnits, IndexedProofSequence)
initialStateWithPropagation f p = do
  z <- initialAssignment (numberVariables f)


  (p', cs) <- fromListAndTranslateProof f p
  l <- lengthCS cs
  w <- initializeWatcher (numberVariables f) l
  -- Filter Unit clauses, we don't need to add them to the clause storage, but can add them directly to the
  -- initial assignment
  let (units', cNU) = L.partition (\cl -> L.length cl == 1) (clauses f)
      units = concat units'
      hasEmptyClause = [] `elem` cNU
  pq <- newMutVar units
  let state = AppState { assignment = z, watcher = w , clauseS = cs, propagationQueue = pq}
  --traceP $ "Initial Clause Storage" ++ show cls
  (pr, pUnits) <- if hasEmptyClause then return (EmptyClauseFound, [])
                  else do
                    setupWatchesForClauseStorage state (numberClauses f)
                    traceD $ "Running initial Unit Propagation with " ++ show units
                    (pr, pUnits) <- propagate state []
                    traceD $ "Initial Unit Propagation ended with implied literals" ++ show pUnits
                    return (pr, pUnits)
  return (state, pr , pUnits, p')





-- * Debugging functions



traceWatcherStats :: (PrimMonad m)
                  => AppState (PrimState m)
                  -> m ()
traceWatcherStats w = do
  l <- V.toList <$> V.unsafeFreeze (watcher w)
  (i, s, m) <- foldM go (0,0,0) l
  let aver = i / fromIntegral s
  traceM $ "Average TwoWatcher Size" ++ show aver
  traceM $ "Maximum TwoWatcher Size" ++ show m
  where
    go (!i,!s, !m) ht = do
      let l = L.length ht
      return (i+1, s+l, max m l)

traceTwoWatcher :: (PrimMonad m)
                => AppState (PrimState m)
                -> m ()
traceTwoWatcher x = do
  --traceTwoWatcher' x
  return ()
--  traceWatcherStats x
--  return ()
traceTwoWatcher' w = do
  traceD $ "================= TWO WATCHER ==================="
  c <- showClausesWithWatches w
  traceD $ "ClauseStorage"
  mapM_ (traceD) $ lines c
  z <- assignmentToList (assignment w)
  traceD $ "Assignment"
  traceD $ show z
  traceD $ "PropagationQueue"
  pQ <- readMutVar (propagationQueue w)
  traceD $ show pQ
  --wat <- (getWatchedClauses w)
  --traceD $ "Watches"
  --traceD $ show wat
  traceD $ "===================== END ======================="


showClausesWithWatches :: (PrimMonad m)
                       => AppState (PrimState m)
                       -> m String
showClausesWithWatches w = do
  l <- getAllWatches w
  -- filter the ones that are not added yet and do a consistency check
  let l' = takeWhile ( not . null . snd ) l

  let caption = "CID - Clause - Clause Interpreted - Watches\n"
  unlines . (caption:) <$> mapM (showClauseWithWatches w) l
  where
    showClauseWithWatches :: (PrimMonad m)
                          => AppState (PrimState m)
                          -> (ClauseId, [Literal])
                          -> m String
    showClauseWithWatches w (cid, watches) = do
      cl <- lookupEntry cid (clauseS w)
      cl' <- do
        r <- analyzeC (assignment w) (clause cl)
        case r of
          ARConflict -> return "[]"
          ARSat -> return "SAT"
          ARUnit l -> return $ show [l]
          AROther l1 l2 -> return $ show (l1, l2)
      return $ show cid ++ " - " ++ show cl ++ " - " ++ show cl' ++ " - " ++ show watches






isLiteralWatchedInClauseId :: (PrimMonad m)
                           => AppState (PrimState m)
                           -> ClauseId
                           -> Literal
                           -> m Bool
isLiteralWatchedInClauseId w i l = do
  watches <- getWatches (watcher w) l
  return $ i `elem` watches

getWatchedLiteralsInClause :: (PrimMonad m)
                           => AppState (PrimState m)
                           -> ClauseId
                           -> m (Maybe [Literal])
getWatchedLiteralsInClause state id = do
  clause <- lookupEntry id (clauseS state)
  r <- getClauseWatches state id
  case r of
    (0, 0) -> return Nothing
    (l1, l2) -> do
      r <- filterM (isLiteralWatchedInClauseId state id) [l1, l2]
      return (Just r)


getAllWatches :: (PrimMonad m)
              => AppState (PrimState m)
              -> m [(ClauseId, [Literal])]
getAllWatches w = do
  ids <- map fst <$> toListWithId (clauseS w)
  watches <- mapM (getWatchedLiteralsInClause w) ids
  let r = map (second fromJust) $ filter (isJust . snd) $ zip ids watches
  return r

verifyProof :: DimacsCNF -> ProofSequence -> Bool
verifyProof f proof = runST $ do
  (f, pr, _, proof') <- initialStateWithPropagation f proof
  case pr of
    EmptyClauseFound -> return True
    _ -> checkRatRefutation f (iClauses proof')


-- * Rup and Rat functions



-- |Returns if a clause is rup with respect to a formula
isRUP :: (PrimMonad m)
         => AppState (PrimState m)
         -> Clause
         -> m (Bool, PropagationUnits) -- Bool
isRUP fol clause = do
  (pr, q) <- exhaustiveUnitPropagation fol (map (\l -> -l) clause)
  case pr of
    EmptyClauseFound -> return (True, q)
    _ -> return (False, q)


-- |Returns if a clause is rup with respect to a formula
isRUPandUndo :: (PrimMonad m)
                => AppState (PrimState m)
                -> Clause
                -> m Bool -- Bool
isRUPandUndo state cl = do
  (res, pr) <- isRUP state cl
  --traceS $ show $ L.sort pr
  undoModifications pr state
  return res

-- |Returns if it is true that clause isNotRAT
checkRAT :: (PrimMonad m)
         => AppState (PrimState m)
         -> Clause
         -> m (Bool, Literal) -- Bool
checkRAT _ [] = error "Got empty clause for rat check"
checkRAT fw cl@(l:_) = do
  b <- checkRATL fw cl l
  return (b, l)

-- |Returns if it is true that clause isNotRAT
checkRATL :: (PrimMonad m)
          => AppState (PrimState m)
          -> Clause
          -> Literal
          -> m Bool -- Bool
checkRATL fw clause lit =
  do
    relevantClauses <- clausesContainingLiteral (-lit) fw
    isNotRAT <- foldM go False relevantClauses
    return isNotRAT
  where
    go st cl = do
      isNotRUP <- isRUPandUndo fw (reduct clause cl lit)
      return (st || isNotRUP)

reduct :: Clause -> Clause -> Literal -> Clause
reduct c d l = filter (/=l) c ++  filter (/= -l) d

-- |Return if the sequence is a valid drat derivation
checkSequence :: (PrimMonad m)
              => AppState (PrimState m)
              -> [IClause]
              -> m Bool
checkSequence st [] = return True
checkSequence st (op:cs) = do
  traceS $ "cs:" ++ show op
  case op of
    (DEL, cid ,_) -> do
      remove cid st
      checkSequence st cs -- FIXME: Wrong behaviour if a unit clause is to be deleted.
    (ADD, _, []) -> do
      traceS $ "Got empty clause in sequence, doing only rup check."
      res <- isRUPandUndo st []
      if res then do
          traceS "rupCheck successful"
          checkSequence st cs
        else do
          traceS "rupCheck failed"
          return False
    (ADD, cid, c) -> do
      isRupCl <- isRUPandUndo st c
      if isRupCl then processClauseAndContinue st cs (cid, c)
      else do
          traceS $ "cs: not rup"
          -- return False
          (isRatCl, lit) <- checkRAT st c
          if isRatCl then processClauseAndContinue st cs (cid, c)
            else do
              traceS $ "cs: also not rat"
              return False
  where
    processClauseAndContinue :: (PrimMonad m)
                             => AppState (PrimState m)
                             -> [IClause]
                             -> (ClauseId, Clause)
                             -> m Bool
    processClauseAndContinue st cs (cid, c) =
      do
        insert cid st
        traceS $ "cs: unit check"
        iu <- isUnit (assignment st) c
        case iu of
          Nothing ->
            do
              traceS $ "cs: not unit; continue "
              checkSequence st cs
          Just l ->
            do
              traceS $ "cs: got unit; propagate it"
              (pr, i2) <- exhaustiveUnitPropagation st [l]
              case pr of
                EmptyClauseFound -> do
                  traceS $ "cs: propagation got a conflict => proven unsatisfiability for all following cases. Stopping"
                  return True -- we have unsatisfiability for all following cases, too, since empty clause can be obtained by unit propagation here
                _ -> do
                  -- we do not have deletion information, therefore dont add it
                  checkSequence st cs



-- Return true if given sequence is a rat refutation
checkRatRefutation :: (PrimMonad m)
                   => AppState (PrimState m)
                   -> [IClause]
                   -> m Bool
checkRatRefutation fw proof = do
  let (relevant, (x:_)) = break (\(op, _, cl) -> op == ADD && null cl) proof
      proof' = relevant ++ [x]
  r <- checkSequence fw proof'
  return ((\(_,_,x) -> x) (L.last proof') == [] && r)


-- ============================================================== MAIN ==========



main :: IO()
main = do
  args <- getArgs

  let cnfFilename = args!!0
      proofFilename = args!!1
  cnfStr <- B.readFile cnfFilename
  proofStr <- B.readFile proofFilename

  let f = parseCNF cnfStr
      proof = parseProof proofStr
  (f, pr, _, proof') <- initialStateWithPropagation f proof
  case pr of
    EmptyClauseFound -> do
      putStrLn "c Initial Unit Propagation found conflict. Done."
      putStrLn "s VERIFIED"
    _ -> do
      pR <- checkRatRefutation f (iClauses proof')
      putStrLn $ if pR then "s VERIFIED" else "s NOT VERIFIED"


importProof :: ProofSequence -> [(Operation, [Literal])]
--importProof = filter ( (==ADD) . fst) .  pClauses
importProof = pClauses
