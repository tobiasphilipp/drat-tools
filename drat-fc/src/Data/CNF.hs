{-# LANGUAGE BangPatterns #-}
module Data.CNF where


import qualified Data.ByteString.Lazy.Char8 as C
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Builder as R
import Data.List (foldl')

type Literal = Int
type Clause = [Literal]
type Formula = [Clause]
compl :: Literal -> Literal
compl !l = -l
{-# INLINE compl #-}

complementC :: Clause -> Formula
complementC = foldl' (\f lit -> [compl lit] : f) []




data DimacsCNF = DimacsCNF
                 { numberVariables :: Int
                 , numberClauses :: Int
                 , clauses :: Formula
                 }

infixr 4 <>
(<>) :: Monoid m => m -> m -> m
(<>) = mappend

showClause :: [Int] -> R.Builder
showClause c = mconcat [(R.intDec l) <> R.char7 ' ' | l <- c]

instance Show DimacsCNF where
  show cnf =
    C.unpack $
    R.toLazyByteString $
    headerLine
    <>
    mconcat [showClause c <> R.char7 ' ' <> R.char7 '0' <> R.char7 '\n' | c <- clauses cnf]
    where
      headerLine = R.string7 "p cnf " <> R.intDec (numberVariables cnf) <> R.char7 ' ' <> R.intDec (numberClauses cnf) <> R.char7 '\n'
