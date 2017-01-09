import           Test.Hspec
import           Test.QuickCheck

import           Test.Lambda.Core.Kinds
import           Test.Lambda.Core.Typecheck

main = hspec $ do
  typecheckSpec
  kindSpec
