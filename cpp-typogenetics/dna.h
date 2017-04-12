#pragma once

#include <cassert>
#include <string>
#include <vector>

enum class Amino : uint8_t {
#define AMINO(b1,b2,mnem,turn,has_effect) \
    mnem##_,
#include "amino.h"
#undef AMINO
};

class Strand;
class Enzyme;

char complementary_base(char x);
bool is_purine(char x);
bool is_pyrimidine(char x);

class Enzyme {
    // Invariant: sequence.size() >= 2.
    // If this weren't true, the concept of "binding preference" would be ill-defined.
    std::vector<Amino> sequence;

public:
    explicit Enzyme(std::vector<Amino> s) : sequence(std::move(s)) { assert(sequence.size() >= 2); }

    char binding_preference() const;
    bool is_noop() const;
    std::vector<Strand> act_upon(const Strand& s, int index_of_binding_site) const;

    friend bool operator==(const Enzyme& a, const Enzyme& b) { return a.sequence == b.sequence; }
    friend bool operator!=(const Enzyme& a, const Enzyme& b) { return a.sequence != b.sequence; }
    friend bool operator<(const Enzyme& a, const Enzyme& b) { return a.sequence < b.sequence; }
};

class Strand {
    std::string bases;

public:
    explicit Strand(std::string b) : bases(std::move(b)) { assert(bases.length() >= 1); }

    std::vector<Enzyme> translate() const;
    int count_binding_sites(char target) const;
    std::string str() const { return bases; }
    bool is_noop() const;
};

inline bool operator==(const Strand& a, const Strand& b) { return a.str() == b.str(); }
inline bool operator!=(const Strand& a, const Strand& b) { return a.str() != b.str(); }
inline bool operator<(const Strand& a, const Strand& b) { return a.str() < b.str(); }
