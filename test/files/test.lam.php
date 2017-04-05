<?php

class Eq {
    public function __construct($eq) {
        $this->eq = $eq;
    }
}

$not = function($b) {
    return (function() use ($b) {
        if ($b === true) {
            return false;
        }
        return true;
    })();
};

$eqBool = new Eq(function($a) use ($not) {
    return function($b) use ($a, $not) {
        return (function() use ($a, $b, $not) {
            if ($a === true) {
                return $b;
            }
            if ($a === false) {
                return $not($b);
            }
        })();
    };
});

$asdf = function($dict37) {
    return function($a) use ($dict37) {
        return ($dict37->eq)($a)($a);
    };
};

$test = $asdf($eqBool)(true);

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

class NilCon {
    public function __construct() {
        $this->values = array();
    }
}

$Nil = new NilCon();

class ConsCon {
    public function __construct($a1, $a2) {
        $this->values = array($a1, $a2);
    }
}

$Cons = function($a1) {
    return function($a2) use ($a1) {
        return new ConsCon($a1, $a2);
    };
};

$eqList = function($dictEq) use ($and) {
    return new Eq((function($dict101) use ($and) {
        return (function() use ($and, $dict101) {
            $eqPrime = function($dict95) use ($and, &$eqPrime) {
                return function($la) use ($and, $dict95, &$eqPrime) {
                    return function($lb) use ($and, $dict95, &$eqPrime, $la) {
                        return (function() use ($and, $dict95, &$eqPrime, $la, $lb) {
                            if ($la instanceof NilCon) {
                                return (function() use (&$eqPrime, $la, $lb) {
                                    if ($lb instanceof NilCon) {
                                        return true;
                                    }
                                    return false;
                                })();
                            }
                            if ($la instanceof ConsCon) {
                                $a = $la->values[0];
                                $laPrime = $la->values[1];
                                return (function() use ($a, $and, $dict95, &$eqPrime, $la, $laPrime, $lb) {
                                    if ($lb instanceof ConsCon) {
                                        $b = $lb->values[0];
                                        $lbPrime = $lb->values[1];
                                        return $and(($dict95->eq)($a)($b))($eqPrime($dict95)($laPrime)($lbPrime));
                                    }
                                    return false;
                                })();
                            }
                        })();
                    };
                };
            };
            return $eqPrime($dict101);
        })();
    })($dictEq));
};

$shouldBeFalse = ($eqList($eqBool)->eq)($Cons(true)($Nil))($Nil);

$shouldBeTrue = ($eqList($eqBool)->eq)($Cons(true)($Nil))($Cons(true)($Nil));

?>
