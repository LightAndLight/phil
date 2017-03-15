<?php

class Eq {
    public function __construct($eq) {
        $this->eq = $eq;
    }
}

$eq = function($dict) {
    return $dict->eq;
};

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

$asdf = (function() use ($eq, $eqBool) {
    $test = function($ev2) use ($eq) {
        return function($a) use ($eq, $ev2) {
            return $eq($ev2)($a)($a);
        };
    };
    return $test($eqBool)(true);
})();

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

$eqList = new Eq(function($ev5) use ($and, $eq) {
    return (function() use ($and, $eq, $ev5) {
        $eqPrime = function($ev4) use ($and, $eq, &$eqPrime, $ev5) {
            return function($la) use ($and, $eq, &$eqPrime, $ev4, $ev5) {
                return function($lb) use ($and, $eq, &$eqPrime, $ev4, $ev5, $la) {
                    return (function() use ($and, $eq, &$eqPrime, $ev4, $ev5, $la, $lb) {
                        if ($la instanceof NilCon) {
                            return (function() use (&$eqPrime, $ev4, $ev5, $la, $lb) {
                                if ($lb instanceof NilCon) {
                                    return true;
                                }
                                return false;
                            })();
                        }
                        if ($la instanceof ConsCon) {
                            $a = $la->values[0];
                            $resta = $la->values[1];
                            return (function() use ($a, $and, $eq, &$eqPrime, $ev4, $ev5, $la, $lb, $resta) {
                                if ($lb instanceof ConsCon) {
                                    $b = $lb->values[0];
                                    $restb = $lb->values[1];
                                    return $and($eq($a)($b))($eqPrime($resta)($restb));
                                }
                                return false;
                            })();
                        }
                    })();
                };
            };
        };
        return $eqPrime($ev5);
    })();
});

$test = $eq($eqListBool)($Cons(true)($Nil))($Cons(true)($Nil));

?>
