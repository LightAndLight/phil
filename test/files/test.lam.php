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

$asdf = function($a) use ($eq) {
    return $eq($a)($a);
};

$test = $asdf(true);

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

$eqList = new Eq((function() use ($and, $eq) {
    $eqPrime = function($la) use ($and, $eq, &$eqPrime) {
        return function($lb) use ($and, $eq, &$eqPrime, $la) {
            return (function() use ($and, $eq, &$eqPrime, $la, $lb) {
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
                    $rest = $la->values[1];
                    return (function() use ($a, $and, $eq, &$eqPrime, $la, $lb, $rest) {
                        if ($lb instanceof ConsCon) {
                            $b = $lb->values[0];
                            $restPrime = $lb->values[1];
                            return $and($eq($a)($b))($eqPrime($rest)($restPrime));
                        }
                        return false;
                    })();
                }
            })();
        };
    };
    return $eqPrime;
})());

$test2 = $asdf($Cons(true)($Nil));

?>
