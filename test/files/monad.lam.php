<?php

class Monad {
    public function __construct($return, $bind) {
        $this->return = $return;
        $this->bind = $bind;
    }
}

$liftM2 = function($dict77) {
    return function($f) use ($dict77) {
        return function($ma) use ($dict77, $f) {
            return function($mb) use ($dict77, $f, $ma) {
                return ($dict77->bind)($ma)(function($a) use ($dict77, $f, $ma, $mb) {
                    return ($dict77->bind)($mb)(function($b) use ($a, $dict77, $f, $ma, $mb) {
                        return ($dict77->return)($f($a)($b));
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

$monadMaybe = new Monad($Just, function($ma) use ($Just, $Nothing) {
    return function($f) use ($Just, $Nothing, $ma) {
        return (function() use ($Just, $Nothing, $f, $ma) {
            if ($ma instanceof NothingCon) {
                return $Nothing;
            }
            if ($ma instanceof JustCon) {
                $a = $ma->values[0];
                return $f($a);
            }
        })();
    };
});

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

$asdf = $liftM2($monadMaybe)($and)($Just(true))($Just(false));

class Show {
    public function __construct($show) {
        $this->show = $show;
    }
}

$showBool = new Show(function($a) use ($Just, $and, $liftM2, $monadMaybe) {
    return (function() use ($Just, $a, $and, $liftM2, $monadMaybe) {
        if ($a === true) {
            return "true";
        }
        if ($a === false) {
            return "false";
        }
    })();
});

$showMaybe = function($dictShow) use ($Just, $and, $liftM2, $monadMaybe) {
    return new Show((function($dict156) use ($Just, $and, $liftM2, $monadMaybe) {
        return function($a) use ($Just, $and, $dict156, $liftM2, $monadMaybe) {
            return (function() use ($Just, $a, $and, $dict156, $liftM2, $monadMaybe) {
                if ($a instanceof NothingCon) {
                    return "Nothing";
                }
                if ($a instanceof JustCon) {
                    $a = $a->values[0];
                    return ($dict156->show)($a);
                }
            })();
        };
    })($dictShow));
};

$test = ($showMaybe($showBool)->show)($asdf);

?>
