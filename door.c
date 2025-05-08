
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

// the data structure containing the state of the keypad
typedef struct {
    uint8_t pin[4];
    uint8_t state;
} keypad;

// new_keypad(pin) returns a keypad data structure in the Locked state with 0 attempts and stored PIN `pin`
keypad new_keypad(uint32_t pin) {
    uint8_t stored[4];
    stored[0] = (pin / 1000) + 1;
    stored[1] = ((pin / 100) % 10) + 1;
    stored[2] = ((pin / 10) % 10) + 1;
    stored[3] = (pin % 10) + 1;
    // creates a new keypad with the input PIN
    keypad kp = { {stored[0], stored[1], stored[2], stored[3]}, 4 };
    return kp;
}

// digit_key(&kp, n) modifies the state of the keypad `kp` as though the digit key `n` had been pressed
void digit_key(keypad* kp, uint8_t n) {
    if (kp->state != 1) {
        int i = 0;
        while (kp->pin[i] >> 4 != 0) {
            ++i;
        }
        kp->pin[i] += (n + 1) << 4;
        if (i == 3) {
            if (kp->state <= 2) {
                for (i = 0; i < 4; ++i) {
                    kp->pin[i] = kp->pin[i] >> 4;
                }
                kp->state += 2;
            }
            else {
                i = 0;
                do {
                    if ((kp->pin[i & 3] >> 4) != (kp->pin[i & 3] & 0x0F)) {
                        i += 12;
                    }
                    ++i;
                } while (i % 4 != 0);
                kp->pin[0] &= 0x0F;
                kp->pin[1] &= 0x0F;
                kp->pin[2] &= 0x0F;
                kp->pin[3] &= 0x0F;
                if (i > 4) {
                    kp->state = (kp->state + 2) % 10;
                }
                else {
                    kp->state = 2;
                }
            }
        }
    }
}
// cancel_key(&kp) modifies the state of the keypad `kp` as though the cancel key had been pressed
void cancel_key(keypad* kp) {
    kp->pin[0] &= 0x0F;
    kp->pin[1] &= 0x0F;
    kp->pin[2] &= 0x0F;
    if (kp->state == 1) {
        kp->state = 4;
    }
}
// cancel_key(&kp) modifies the state of the keypad `kp` as though the accept key had been pressed
void accept_key(keypad* kp) {
    if (kp->state == 2) {
        kp->state = 1;
    }
}

// is_open(&kp) returns `true` if the door is the Open state, and `false` otherwise
bool is_open(keypad* kp) {
    return kp->state == 1;
}

int main(int argc, char* argv[]) {
    uint32_t pin = 0;
    char* c = argv[1];
    // recovers the PIN as a decimal number from the first argument
    while (*c) {
        pin *= 10;
        pin += *c - 48;
        c++;
    }
    // creates a new keypad with the input PIN
    keypad kp = new_keypad(pin);
    c = argv[2];
    // calls the corresponding function for each input character in the second argument
    while (*c) {
        if (*c == 65) {
            accept_key(&kp);
        }
        else if (*c == 67) {
            cancel_key(&kp);
        }
        else {
            digit_key(&kp, *c - 48);
        }
        ++c;
    }
    // tests if the door is open after receiving the input
    if (is_open(&kp)) {
        printf("door is open\n");
        exit(0);
    }
    else {
        printf("door is closed\n");
        exit(1);
    }
}

void check_key(keypad* kp, char c) {
    if (c == 65) {
        accept_key(kp);
    }
    else if (c == 67) {
        cancel_key(kp);
    }
    else {
        digit_key(kp, c - 48);
    }
}

bool is_unlocked(keypad* kp) {
    return kp->state == 2;
}

bool is_blocked(keypad* kp) {
    return kp->state == 0;
}