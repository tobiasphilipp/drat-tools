{-# LANGUAGE OverloadedStrings #-}
{- -*- mode: haskell; mode: haskell-indentation; mode: interactive-haskell  -*-
Module      : Data.Parse.DRAT
Description : A library that reads DRAT files in DIMACS format
Copyright   : (c) Tobias Philipp and Walter Forkel 2016
Maintainer  : walter.forkel@tu-dresden.de
Stability   : experimental
Portability : POSIX

longer description
-}

-- TODO: Extend to parse deletion information in RUP format

module Data.Parse.DRAT
       (
         parseProof
       )
       where

import System.Environment

import           Data.Monoid hiding ((<>))

import qualified Data.ByteString.Lazy.Char8 as C
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Builder as R
import Data.Maybe (fromJust)

import Data.DRAT
import Data.CNF

myWords s = filter (/= ws) $ B.split ' ' s
  where
    ws = B.pack ""


parseClauseLine s = init $ map (fst . fromJust . B.readInt) $ myWords s
ltrim = B.dropWhile (== ' ')

normalize :: B.ByteString -> [B.ByteString]
normalize = filter relevant . map ltrim . B.lines
  where
    relevant = (\s -> not $ (B.isPrefixOf "c" s) || s == B.pack "" || (B.isPrefixOf "s" s) )

readOperation :: B.ByteString -> (Operation, B.ByteString)
readOperation s = if B.head s == 'd' then (DEL, B.drop 2 s)
                  else (ADD, s)

parseProof :: B.ByteString -> ProofSequence
parseProof ss = ProofSequence { pNumSteps = length cs, pClauses = cs }
  where
    preparse = normalize ss
    cs = map parseLine preparse
    parseLine s = h $ readOperation s
    h (op, s) = (op, parseClauseLine s)
