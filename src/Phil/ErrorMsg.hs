module Phil.ErrorMsg where

import Text.PrettyPrint.ANSI.Leijen

errorMsg
  :: String -- ^ Message title
  -> Doc -- ^ Message body
  -> Doc
errorMsg title body
  = vcat
    [ text title
    , text $ fmap (const '-') title
    , text ""
    , body
    ]
