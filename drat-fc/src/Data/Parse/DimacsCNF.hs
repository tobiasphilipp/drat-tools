{-# LANGUAGE OverloadedStrings #-}
{- -*- mode: haskell; mode: haskell-indentation; mode: interactive-haskell  -*-
Module      : DimacsCNF
Description : A library that reads CNF files in DIMACS format
Copyright   : (c) Tobias Philipp and Walter Forkel 2016
Maintainer  : walter.forkel@tu-dresden.de
Stability   : experimental
Portability : POSIX

longer description
-}

-- TODO: Extend to parse deletion information in RUP format

module Data.Parse.DimacsCNF
       (
         parseCNF,
       )
       where

import System.Environment

import           Data.Monoid hiding ((<>))

import qualified Data.ByteString.Lazy.Char8 as C
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Builder as R
import Data.Maybe (fromJust)

import Data.CNF

myWords s = filter (/= ws) $ B.split ' ' s
  where
    ws = B.pack ""


parseClauseLine s = init $ map (fst . fromJust . B.readInt) $ myWords s

ltrim = B.dropWhile (== ' ')

normalize :: B.ByteString -> [B.ByteString]
normalize = filter relevant . map ltrim . B.lines
  where
    relevant = (\s -> not $ (B.isPrefixOf "c" s) || s == B.pack "")

parsePCNFHeader s = (numC, numV)
  where
    (Just (numV, _)) = (B.readInt $ (myWords s)!!2)
    (Just (numC, _)) = (B.readInt $ (myWords s)!!3)

parseCNF :: B.ByteString -> DimacsCNF
parseCNF s = DimacsCNF {numberClauses = numC, numberVariables = numV, clauses = cs}
  where
    (numC, numV) = parsePCNFHeader $ head preparse
    cs = map parseClauseLine $ tail preparse
    preparse = normalize s
