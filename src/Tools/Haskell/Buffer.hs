{- GENERATED by Isabelle! -}
{-  Title:      Tools/Haskell/Buffer.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Efficient text buffers.
-}

module Isabelle.Buffer (T, empty, add, content)
where

newtype T = Buffer [String]

empty :: T
empty = Buffer []

add :: String -> T -> T
add "" buf = buf
add x (Buffer xs) = Buffer (x : xs)

content :: T -> String
content (Buffer xs) = concat (reverse xs)
