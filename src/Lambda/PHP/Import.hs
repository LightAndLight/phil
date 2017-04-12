module Lambda.PHP.Import where

import Control.Monad.IO.Class

bootstrapImport :: MonadIO m => FilePath -> m ()
bootstrapImport fp
  = liftIO . writeFile fp $
    unlines
      [ "<?php"
      , ""
      , "$import = function ($module_name) {"
      , "    include $module_name;"
      , "    return $exports;"
      , "}"
      , ""
      , "?>"
      ]
