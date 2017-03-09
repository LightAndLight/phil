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

$id = function($x) {
    return $x;
};

$idPrime = $id;

?>
