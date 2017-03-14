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

$test = function($ev2) use ($eq) {
    return function($a) use ($eq, $ev2) {
        return $eq($ev2)($a)($a);
    };
};

$asdf = $test($eqBool)(true);

?>
