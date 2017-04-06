<?php

class Functor {
    public function __construct($fmap) {
        $this->fmap = $fmap;
    }
}

class Applicative {
    public function __construct($pure, $ap, $Functor) {
        $this->pure = $pure;
        $this->ap = $ap;
        $this->Functor = $Functor;
    }
}

class Monoid {
    public function __construct($mempty, $mappend) {
        $this->mempty = $mempty;
        $this->mappend = $mappend;
    }
}

class ConstCon {
    public function __construct($a1) {
        $this->values = array($a1);
    }
}

$Const = function($a1) {
    return new ConstCon($a1);
};

$pureConst = function($dict55) use ($Const) {
    return function($a) use ($Const, $dict55) {
        return $Const($dict55->mempty);
    };
};

$apConst = function($dict101) use ($Const) {
    return function($a) use ($Const, $dict101) {
        return function($b) use ($Const, $a, $dict101) {
            return (function() use ($Const, $a, $b, $dict101) {
                if ($a instanceof ConstCon) {
                    $aa = $a->values[0];
                    return (function() use ($Const, $a, $aa, $b, $dict101) {
                        if ($b instanceof ConstCon) {
                            $bb = $b->values[0];
                            return $Const(($dict101->mappend)($aa)($bb));
                        }
                    })();
                }
            })();
        };
    };
};

$fmapConst = function($f) use ($Const) {
    return function($cm) use ($Const) {
        return (function() use ($Const, $cm) {
            if ($cm instanceof ConstCon) {
                $m = $cm->values[0];
                return $Const($m);
            }
        })();
    };
};

$functorConst = function($dictMonoid) use ($Const) {
    return new Functor((function($f) use ($Const) {
        return function($cm) use ($Const) {
            return (function() use ($Const, $cm) {
                if ($cm instanceof ConstCon) {
                    $m = $cm->values[0];
                    return $Const($m);
                }
            })();
        };
    })($dictMonoid));
};

$applicativeConst = function($dictMonoid) use ($Const, $apConst, $functorConst, $pureConst) {
    return new Applicative((function($dict159) use ($Const, $dictMonoid, $pureConst) {
        return $pureConst($dict159);
    })($dictMonoid), (function($dict167) use ($Const, $apConst, $dictMonoid, $pureConst) {
        return $apConst($dict167);
    })($dictMonoid), $functorConst($dictMonoid));
};

$liftA2 = function($dict214) {
    return function($f) use ($dict214) {
        return function($ma) use ($dict214, $f) {
            return function($mb) use ($dict214, $f, $ma) {
                return ($dict214->ap)(($dict214->Functor->fmap)($f)($ma))($mb);
            };
        };
    };
};

?>
