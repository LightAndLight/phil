module Lambda.PHP.Import where

bootstrapImport :: FilePath -> IO ()
bootstrapImport fp
  = writeFile fp $
    unlines
      [ "<?php"
      , ""
      , "function import($module_name) {"
      , "    include $module_name . \".php\";"
      , "    return $exports;"
      , "}"
      , ""
      , "?>"
      ]
