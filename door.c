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
    if (kp->state > 1) {
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

unsigned int nondet_uint();
char nondet_char();

//Case: "Pressing C does not close the door if it is open."
void cancel_key_closes_door() {

    unsigned int pin = nondet_uint();
    __CPROVER_assume(pin <= 9999);
    __CPROVER_assume(pin >= 0000);

    keypad kp = new_keypad(pin);

    unsigned int attempt1 = 0;
    char str[4];

    for (int i = 0; i < 4; i++) {
        char c = nondet_char();
        __CPROVER_assume(48 <= c && c <= 57);
        attempt1 *= 10;
        attempt1 += c - 48;
        str[i] = c;
        check_key(&kp, str[i]);
    }

    __CPROVER_assume(attempt1 == pin);
    __CPROVER_assert(is_unlocked(&kp) == true, "Unlocked");

    accept_key(&kp);
    __CPROVER_assert(is_unlocked(&kp) == false && is_open(&kp) == true, "Open");

    cancel_key(&kp);

    __CPROVER_assert(is_unlocked(&kp) == false && is_open(&kp) == false, "Locked");
}

//Case: "A locked door can be unlocked without introducing the correct PIN.'
void wrong_pin_does_not_open_door() {

    unsigned int pin = nondet_uint();
    __CPROVER_assume(pin <= 9999);
    __CPROVER_assume(pin >= 0000);

    keypad kp = new_keypad(pin);

    unsigned int attempt1 = 0;
    char str[4];

    for (int i = 0; i < 4; i++) {
        char c = nondet_char();
        __CPROVER_assume(48 <= c && c <= 57);
        attempt1 *= 10;
        attempt1 += c - 48;
        str[i] = c;
        check_key(&kp, str[i]);
    }

    __CPROVER_assume(attempt1 != pin);
    accept_key(&kp);

    __CPROVER_assert(is_unlocked(&kp) == false && is_open(&kp) == false, "Locked");
}

//Case: "The stored PIN cannot be changed into any arbitrary PIN. && 
//Case: "The door is not closed and locked after changing the stored PIN."
void pin_can_be_changed_and_locked() {

    unsigned int pin = nondet_uint();
    __CPROVER_assume(pin <= 9999);
    __CPROVER_assume(pin >= 0000);

    keypad kp = new_keypad(pin);

    unsigned int attempt1 = 0;
    char str[4];

    for (int i = 0; i < 4; i++) {
        char c = nondet_char();
        __CPROVER_assume(48 <= c && c <= 57);
        attempt1 *= 10;
        attempt1 += c - 48;
        str[i] = c;
        check_key(&kp, str[i]);
    }

    __CPROVER_assume(attempt1 == pin);
    __CPROVER_assert(is_unlocked(&kp) == true, "Unlocked");

    attempt1 = 0;

    for (int i = 0; i < 4; i++) {
        char c = nondet_char();
        __CPROVER_assume(48 <= c && c <= 57);
        attempt1 *= 10;
        attempt1 += c - 48;
        str[i] = c;
        check_key(&kp, str[i]);
    }

    __CPROVER_assume(attempt1 != pin);
    pin = &attempt1;
    __CPROVER_assert(is_unlocked(&kp) == false && is_open(&kp) == false, "Locked");

    attempt1 = 0;

    for (int i = 0; i < 4; i++) {
        char c = nondet_char();
        __CPROVER_assume(48 <= c && c <= 57);
        attempt1 *= 10;
        attempt1 += c - 48;
        str[i] = c;
        check_key(&kp, str[i]);
    }

    __CPROVER_assume(attempt1 = pin);
    __CPROVER_assert(is_unlocked(&kp) == true && is_open(&kp) == false, "Unlocked");
    accept_key(&kp);
    __CPROVER_assert(is_unlocked(&kp) == false && is_open(&kp) == true, "Open");
}

void door_blocked_after_three_attempts() {

    unsigned int pin = nondet_uint();
    __CPROVER_assume(pin <= 9999);
    __CPROVER_assume(pin >= 0000);

    keypad kp = new_keypad(pin);

    unsigned int attempt1 = 0;
    char str[4];

    for (int i = 0; i < 3; i++) {
        for (int i = 0; i < 4; i++) {
            char c = nondet_char();
            __CPROVER_assume(48 <= c && c <= 57);
            attempt1 *= 10;
            attempt1 += c - 48;
            str[i] = c;
            check_key(&kp, str[i]);
        }
        __CPROVER_assume(attempt1 != pin);
        __CPROVER_assert(is_unlocked(&kp) == false && is_open(&kp) == false, "Locked");
        attempt1 = 0;
    }

    __CPROVER_assert(is_blocked(&kp) == true, "Blocked");

    for (int i = 0; i < 4; i++) {
        char c = nondet_char();
        __CPROVER_assume(48 <= c && c <= 57);
        attempt1 *= 10;
        attempt1 += c - 48;
        str[i] = c;
        check_key(&kp, str[i]);
    }

    __CPROVER_assume(attempt1 == pin);
    __CPROVER_assert(is_blocked(&kp) == true, "Blocked");
}