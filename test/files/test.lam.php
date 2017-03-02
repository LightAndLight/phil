<?php

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

$ifte = function($cond) {
    return function($a) use ($cond) {
        return function($b) use ($a, $cond) {
            return (function() use ($a, $b, $cond) {
                if ($cond === true) {
                    return $a;
                }
                if ($cond === false) {
                    return $b;
                }
            })();
        };
    };
};

$filter = (function() use ($Cons, $Nil, $ifte) {
    $filterPrime = function($pred) use ($Cons, $Nil, &$filterPrime, $ifte) {
        return function($list) use ($Cons, $Nil, &$filterPrime, $ifte, $pred) {
            return (function() use ($Cons, $Nil, &$filterPrime, $ifte, $list, $pred) {
                if ($list instanceof NilCon) {
                    return $Nil;
                }
                if ($list instanceof ConsCon) {
                    $a = $list->values[0];
                    $rest = $list->values[1];
                    return $ifte($pred($a))($Cons($a)($filterPrime($pred)($rest)))($filterPrime($pred)($rest));
                }
            })();
        };
    };
    return $filterPrime;
})();

$test = $filter(function($x) use ($filter) {
    return $x;
})($Cons(true)($Cons(false)($Cons(true)($Nil))));

?>
