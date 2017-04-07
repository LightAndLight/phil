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

$liftM2 = function($dict101) {
    return function($f) use ($dict101) {
        return function($ma) use ($dict101, $f) {
            return function($mb) use ($dict101, $f, $ma) {
                return ($dict101->bind)($ma)(function($a) use ($dict101, $f, $ma, $mb) {
                    return ($dict101->bind)($mb)(function($b) use ($a, $dict101, $f, $ma, $mb) {
                        return ($dict101->Applicative->pure)($f($a)($b));
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
                retur