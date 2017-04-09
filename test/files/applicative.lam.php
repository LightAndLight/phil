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

$pureConst = function($dict69) use ($Const) {
    return function($a) use ($Const, $dict69) {
        return $Const($dict69->mempty);
    };
};

$apConst = function($dict120) use ($Const) {
    return function($a) use ($Const, $dict120) {
        return function($b) use ($Const, $a, $dict120) {
            return (function() use ($Const, $a, $b, $dict120) {
                if ($a instanceof ConstCon) {
                    $aa = $a->values[0];
                    return (function() use ($Const, $a, $aa, $b, $dict120) {
                        if ($b instanceof ConstCon) {
                            $bb = $b->values[0];
                            return $Const(($dict120->mappend)($aa)($bb));
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

$liftA2 = function($dict311) {
    return function($f) use ($dict311) {
        return function($ma) use ($dict311, $f) {
            return function($mb) use ($dict311, $f, $ma) {
                return ($dict311->ap)(($dict311->Functor->fmap)($f)($ma))($mb);
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
