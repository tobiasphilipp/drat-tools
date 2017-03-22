module Data.DRAT where

import Data.CNF


import qualified Data.ByteString.Lazy.Char8 as C
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Builder as R


data Operation = ADD | DEL
               deriving (Eq, Show)

type DClause = (Operation, Clause)

type ClauseId = Int
type IClause = (Operation, ClauseId, Clause)




data ProofSequence = ProofSequence
                   {  pNumSteps :: Int
                   ,  pClauses :: [DClause] }
    deriving (Eq, Show)
data IndexedProofSequence = IndexedProofSequence
                   {  iNumSteps :: Int
                   ,  iClauses :: [IClause] }
    deriving (Eq, Show)


showProof :: ProofSequence -> C.ByteString
showProof (ProofSequence _ p) =
    R.toLazyByteString $
    mconcat [(if op == ADD then R.char7 ' ' else R.char7 'd') <>  R.char7 ' ' <> showClause c <> R.char7 ' ' <> R.char7 '0' <> R.char7 '\n' | (op, c) <- p]

reverseProofSequence p = p {pClauses = reverse (pClauses p)}
