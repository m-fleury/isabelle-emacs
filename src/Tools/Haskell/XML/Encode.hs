{- generated by Isabelle -}

{-  Title:      Tools/Haskell/XML/Encode.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

XML as data representation language.

See also "$ISABELLE_HOME/src/Pure/PIDE/xml.ML".
-}

module Isabelle.XML.Encode (
  A, T, V,

  int_atom, bool_atom, unit_atom,

  tree, properties, string, init, bool, unit, pair, triple, list, variant
)
where

import Isabelle.Library
import qualified Isabelle.Value as Value
import qualified Isabelle.Properties as Properties
import qualified Isabelle.XML as XML


type A a = a -> String
type T a = a -> XML.Body
type V a = a -> Maybe ([String], XML.Body)


-- atomic values

int_atom :: A Int
int_atom = Value.print_int

bool_atom :: A Bool
bool_atom False = "0"
bool_atom True = "1"

unit_atom :: A ()
unit_atom () = ""


-- structural nodes

node = XML.Elem (":", [])

vector = map_index (\(i, x) -> (int_atom i, x))

tagged (tag, (xs, ts)) = XML.Elem (int_atom tag, vector xs) ts


-- representation of standard types

tree :: T XML.Tree
tree t = [t]

properties :: T Properties.T
properties props = [XML.Elem (":", props) []]

string :: T String
string "" = []
string s = [XML.Text s]

int :: T Int
int = string . int_atom

bool :: T Bool
bool = string . bool_atom

unit :: T ()
unit = string . unit_atom

pair :: T a -> T b -> T (a, b)
pair f g (x, y) = [node (f x), node (g y)]

triple :: T a -> T b -> T c -> T (a, b, c)
triple f g h (x, y, z) = [node (f x), node (g y), node (h z)]

list :: T a -> T [a]
list f xs = map (node . f) xs

variant :: [V a] -> T a
variant fs x = [tagged (the (get_index (\f -> f x) fs))]
