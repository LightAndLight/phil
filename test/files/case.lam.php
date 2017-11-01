<?php

$test = (function() {
    if (true === true) {
        return 1;
    }
    if (true === false) {
        return 2;
    }
})();

?>
