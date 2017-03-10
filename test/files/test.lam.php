<?php

class LTCon {
    public function __construct() {
        $this->values = array();
    }
}

$LT = new LTCon();

class EQCon {
    public function __construct() {
        $this->values = array();
    }
}

$EQ = new EQCon();

class GTCon {
    public function __construct() {
        $this->values = array();
    }
}

$GT = new GTCon();

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

$thing = function($a) use ($and, $eq) {
    return function($b) use ($a, $and, $eq) {
        return $and($eq($a)($a))($eq($b)($b));
    };
};

$thing2 = function($a) use ($thing) {
    return $thing($a)($a);
};

?>
