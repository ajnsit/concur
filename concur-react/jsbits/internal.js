#include <ghcjs/rts.h>

function h$concurEventCallback(async, action, ev) {
    var a = MK_AP1(action, MK_JSVAL(ev));
    if(async) {
        h$run(a);
    } else {
        h$runSync(a, true);
    }
}
