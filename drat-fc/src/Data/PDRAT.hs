module Data.PDRAT where

import Data.CNF
import Data.DRAT

type PClause = (Operation, Int, Clause)

data ParallelProofSequence = ParallelProofSequence
                              { ppNumFormulas :: Int -- ^ The number of parallel instances
                              , ppNumSteps :: Int
                              , ppClauses :: [PClause] }


dratToPdrat :: ProofSequence -> ParallelProofSequence
dratToPdrat (ProofSequence i cs) = ParallelProofSequence 1 i (map (\(o, c) -> (o, 1, c)) cs)
