import           Test.Hspec
import           Test.QuickCheck

import           Test.Lambda.Core.Kinds
import           Test.Lambda.Core.Typecheck
import           Test.Lambda.Core.Typeclasses

main = hspec $ do
  typecheckSpec
  kindSpec
  typeclassesSpec
