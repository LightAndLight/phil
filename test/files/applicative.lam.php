<?php

class Functor {
    public function __construct($fmap) {
        $this->fmap = $fmap;
    }
}

class Applicative {
    public function __construct($pure, $ap, $super1) {
        $this->pure = $pure;
        $this->ap = $ap;
        $this->fmap = $super1->fmap;
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

$pureConst = function($dict60) use ($Const) {
    return function($a) use ($Const, $dict60) {
        return $Const($dict60->mempty);
    };
};

$apConst = function($dict106) use ($Const) {
    return function($a) use ($Const, $dict106) {
        return function($b) use ($Const, $a, $dict106) {
            return (function() use ($Const, $a, $b, $dict106) {
                if ($a instanceof ConstCon) {
                    $aa = $a->values[0];
                    return (function() use ($Const, $a, $aa, $b, $dict106) {
                        if ($b instanceof ConstCon) {
                            $bb = $b->values[0];
                            return $Const(($dict106->mappend)($aa)($bb));
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
    return new Applicative((function($dict164) use ($Const, $dictMonoid, $pureConst) {
        return $pureConst($dict164);
    })($dictMonoid), (function($dict172) use ($Const, $apConst, $dictMonoid, $pureConst) {
        return $apConst($dict172);
    })($dictMonoid), $functorConst);
};

$liftA2 = function($dict219) {
    return function($f) use ($dict219) {
        return function($ma) use ($dict219, $f) {
            return function($mb) use ($dict219, $f, $ma) {
                return ($dict219->ap)(($dict219->fmap)($f)($ma))($mb);
            };
        };
    };
};

echo $liftA2($applicativeConst("b"))($Const("a"))($Const("b"))($Const("c"));

?>
