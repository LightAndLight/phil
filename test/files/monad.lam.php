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

class Monad {
    public function __construct($bind, $Applicative) {
        $this->bind = $bind;
        $this->Applicative = $Applicative;
    }
}

$liftM2 = function($dict111) {
    return function($f) use ($dict111) {
        return function($ma) use ($dict111, $f) {
            return function($mb) use ($dict111, $f, $ma) {
                return ($dict111->bind)($ma)(function($a) use ($dict111, $f, $ma, $mb) {
                    return ($dict111->bind)($mb)(function($b) use ($a, $dict111, $f, $ma, $mb) {
                        return ($dict111->Applicative->pure)($f($a)($b));
                    });
                });
            };
        };
    };
};

class NothingCon {
    public function __construct() {
        $this->values = array();
    }
}

$Nothing = new NothingCon();

class JustCon {
    public function __construct($a1) {
        $this->values = array($a1);
    }
}

$Just = function($a1) {
    return new JustCon($a1);
};

$functorMaybe = new Functor(function($f) use ($Just, $Nothing) {
    return function($ma) use ($Just, $Nothing, $f) {
        return (function() use ($Just, $Nothing, $f, $ma) {
            if ($ma instanceof NothingCon) {
                return $Nothing;
            }
            if ($ma instanceof JustCon) {
                $a = $ma->values[0];
                return $Just($f($a));
            }
        })();
    };
});

$applicativeMaybe = new Applicative($Just, function($mf) use ($Just, $Nothing) {
    return function($ma) use ($Just, $Nothing, $mf) {
        return (function() use ($Just, $Nothing, $ma, $mf) {
            if ($mf instanceof NothingCon) {
                return $Nothing;
            }
            if ($mf instanceof JustCon) {
                $f = $mf->values[0];
                return (function() use ($Just, $Nothing, $f, $ma, $mf) {
                    if ($ma instanceof NothingCon) {
                        return $Nothing;
                    }
                    if ($ma instanceof JustCon) {
                        $a = $ma->values[0];
                        return $Just($f($a));
                    }
                })();
            }
        })();
    };
}, $functorMaybe);

$monadMaybe = new Monad(function($ma) use ($Just, $Nothing, $functorMaybe) {
    return function($f) use ($Just, $Nothing, $functorMaybe, $ma) {
        return (function() use ($Just, $Nothing, $f, $functorMaybe, $ma) {
            if ($ma instanceof NothingCon) {
                return $Nothing;
            }
            if ($ma instanceof JustCon) {
                $a = $ma->values[0];
                return $f($a);
            }
        })();
    };
}, $applicativeMaybe);

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

class Show {
    public function __construct($show) {
        $this->show = $show;
    }
}

$showBool = new Show(function($a) {
    return (function() use ($a) {
        if ($a === true) {
            return "true";
        }
        if ($a === false) {
            return "false";
        }
    })();
});

$showMaybe = function($dictShow) {
    return new Show(function($a) use ($dictShow) {
        return (function() use ($a, $dictShow) {
            if ($a instanceof NothingCon) {
                return "Nothing";
            }
            if ($a instanceof JustCon) {
                $a = $a->values[0];
                return ($dictShow->show)($a);
            }
        })();
    });
};

$not = function($a) {
    return (function() use ($a) {
        if ($a === true) {
            return false;
        }
        return true;
    })();
};

$asdf = function($dict396) use ($and, $liftM2, $not) {
    return function($a) use ($and, $dict396, $liftM2, $not) {
        return function($b) use ($a, $and, $dict396, $liftM2, $not) {
            return ($dict396->Applicative->Functor->fmap)($not)($liftM2($dict396)($and)($a)($b));
        };
    };
};

$test = ($showMaybe($showBool)->show)($asdf($monadMaybe)($Just(true))($Just(true)));

?>
