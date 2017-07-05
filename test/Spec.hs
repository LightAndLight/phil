import           Test.Hspec
import           Test.QuickCheck

import           Test.Phil.Core.Kinds
import           Test.Phil.Core.Typecheck
import           Test.Phil.Core.Typeclasses

main = hspec $ do
  typecheckSpec
  kindSpec
  typeclassesSpec
