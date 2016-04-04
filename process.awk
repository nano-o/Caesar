BEGIN { erase=0 }
/^.*bal =.*/ { erase=1 }
/^.*com =.*/ { erase=1 }
/^.*stack =.*/ { erase=1 }
/^.*pc =.*/ { erase=1 }
/^.*propose =.*/ { erase=0 }
/^.*estimate =.*/ { erase=0 }
/^.*join =.*/ { erase=0 }
/^.*retry =.*/ { erase=0 }
/^.*ballot =.*/ { erase=0 }
/^.*stable =.*/ { erase=0 }
/^.*whitelist =.*/ { erase=0 }
{if (erase == 0) { print $0 } }

