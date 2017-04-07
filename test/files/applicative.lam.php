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

$pureConst = function($dict54) use ($Const) {
    return function($a) use ($Const, $dict54) {
        return $Const($dict54->mempty);
    };
};

$apConst = function($dict99) use ($Const) {
    return function($a) use ($Const, $dict99) {
        return function($b) use ($Const, $a, $dict99) {
            return (function() use ($Const, $a, $b, $dict99) {
                if ($a instanceof ConstCon) {
                    $aa = $a->values[0];
                    return (function() use ($Const, $a, $aa, $b, $dict99) {
                        if ($b instanceof ConstCon) {
                            $bb = $b->values[0];
                            return $Const(($dict99->mappend)($aa)($bb));
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
    return new Functor(function($f) use ($Const) {
        return function($cm) use ($Const) {
            return (function() use ($Const, $cm) {
                if ($cm instanceof ConstCon) {
                    $m = $cm->values[0];
                    return $Const($m);
                }
            })();
        };
    });
};

$applicativeConst = function($dictMonoid) use ($Const, $apConst, $functorConst, $pureConst) {
    return new Applicative($pureConst($dictMonoid), $apConst($dictMonoid), $functorConst($dictMonoid));
};

$liftA2 = function($dict234) {
    return function($f) use ($dict234) {
        return function($ma) use ($dict234, $f) {
            return function($mb) use ($dict234, $f, $ma) {
                return ($dict234->ap)(($dict234->Functor->fmap)($f)($ma))($mb);
            };
        };
    };
};

$and = function($a) {
    return function($b) use ($a) {
        return (function() use ($a, $b) {
            if ($a === true) {
                return $b;
            }
            return false;
        })();
    };
};

$monoidBool = new Monoid(true, $and);

$test = $liftA2($applicativeConst($monoidBool))($and)($Const(true))($Const(false));

?>
