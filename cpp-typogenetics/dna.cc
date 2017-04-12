
#include "dna.h"
#include <algorithm>
#include <cassert>
#include <string>
#include <vector>

static std::string reverse(std::string s)
{
    std::reverse(s.begin(), s.end());
    return s;
}

char complementary_base(char x)
{
    if (x == 'A') return 'T';
    if (x == 'C') return 'G';
    if (x == 'G') return 'C';
    if (x == 'T') return 'A';
    assert(false);
    __builtin_unreachable();
}

bool is_purine(char x)
{
    return (x == 'A' || x == 'G');
}

bool is_pyrimidine(char x)
{
    return (x == 'C' || x == 'T');
}

static Amino amino_from_basepair(char i, char j)
{
#define AMINO(b1,b2,mnem,turn,has_effect) \
    if (i==#b1[0] && j==#b2[0]) return Amino::mnem##_;
#include "amino.h"
#undef AMINO
    assert(false);
    __builtin_unreachable();
}

char Enzyme::binding_preference() const
{
    int dir = 0;
    constexpr int s = 0;
    constexpr int l = 1;
    constexpr int r = 3;
    for (int i=1; i < sequence.size()-1; ++i) {
        switch (sequence[i]) {
#define AMINO(b1,b2,mnem,turn,has_effect) \
            case Amino::mnem##_: dir += turn; dir %= 4; break;
#include "amino.h"
#undef AMINO
            default: assert(false);
        }
    }
    switch (dir) {
        case 0: return 'A';
        case 1: return 'C';
        case 3: return 'G';
        case 2: return 'T';
    }
    assert(false);
    __builtin_unreachable();
}

bool Enzyme::is_noop() const
{
    for (Amino a : sequence) {
        switch (a) {
#define AMINO(b1,b2,mnem,turn,has_effect) \
            case Amino::mnem##_: if (has_effect) return false; break;
#include "amino.h"
#undef AMINO
        }
    }
    return true;
}

bool Strand::is_noop() const
{
    for (auto&& e : translate()) {
        if (!e.is_noop()) {
            return false;
        }
    }
    return true;
}

std::vector<Enzyme> Strand::translate() const
{
    std::vector<Enzyme> result;
    std::vector<Amino> current_enzyme;
    for (int i=0; i+1 < bases.length(); i += 2) {
        if (bases[i] == 'A' && bases[i+1] == 'A') {
            if (current_enzyme.size() >= 2) {
                result.emplace_back(std::move(current_enzyme));
            }
            current_enzyme.clear();
        } else {
            current_enzyme.push_back(amino_from_basepair(bases[i], bases[i+1]));
        }
    }
    if (current_enzyme.size() >= 2) {
        result.emplace_back(std::move(current_enzyme));
    }
    return result;
}

int Strand::count_binding_sites(char target) const
{
    return std::count(bases.begin(), bases.end(), target);
}

std::vector<Strand> Enzyme::act_upon(const Strand& strand, int index_of_binding_site) const
{
    std::string bound_strand = strand.str();

    int pos = [&]() {
        int pos = -1;
        const char target = this->binding_preference();
        for (int i=0; i <= index_of_binding_site; ++i) {
            pos = bound_strand.find(target, pos+1);
        }
        assert(0 <= pos && pos < bound_strand.length());
        return pos;
    }();

    if (pos == -1) {
        return {strand};
    }

    std::string opposite_strand(bound_strand.length(), ' ');
    bool copy_mode = false;
    bool finished = false;
    std::vector<Strand> pool;

    auto maybe_add_to_pool = [&](std::string s) {
        std::string candidate;
        for (char b : s) {
            if (b == ' ') {
                if (!candidate.empty()) {
                    pool.emplace_back(std::move(candidate));
                    candidate.clear();
                }
            } else {
                candidate += b;
            }
        }
        if (!candidate.empty()) {
            pool.emplace_back(std::move(candidate));
        }
    };

    for (Amino a : sequence) {
        if (finished) {
            break;
        }
        switch (a) {
            case Amino::cut_: {
                if (pos != bound_strand.length()) {
                    maybe_add_to_pool(bound_strand.substr(pos+1));
                    maybe_add_to_pool(reverse(opposite_strand.substr(pos+1)));
                    bound_strand.resize(pos+1);
                    opposite_strand.resize(pos+1);
                }
                break;
            }
            case Amino::del_: {
                if (opposite_strand[pos] == ' ') {
                    bound_strand.erase(pos, 1);
                    opposite_strand.erase(pos, 1);
                } else {
                    bound_strand[pos++] = ' ';
                }
                if (pos == bound_strand.length() || bound_strand[pos] == ' ') {
                    finished = true;
                }
                break;
            }
            case Amino::swi_: {
                auto temp = reverse(std::move(bound_strand));
                bound_strand = reverse(std::move(opposite_strand));
                opposite_strand = std::move(temp);
                pos = bound_strand.length() - pos - 1;
                if (bound_strand[pos] == ' ') {
                    finished = true;
                }
                break;
            }
            case Amino::mvr_: {
                pos += 1;
                if (pos == bound_strand.length() || bound_strand[pos] == ' ') {
                    finished = true;
                } else if (copy_mode) {
                    opposite_strand[pos] = complementary_base(bound_strand[pos]);
                }
                break;
            }
            case Amino::mvl_: {
                pos -= 1;
                if (pos == -1 || bound_strand[pos] == ' ') {
                    finished = true;
                } else if (copy_mode) {
                    opposite_strand[pos] = complementary_base(bound_strand[pos]);
                }
                break;
            }
            case Amino::cop_: {
                copy_mode = true;
                opposite_strand[pos] = complementary_base(bound_strand[pos]);
                break;
            }
            case Amino::off_: {
                copy_mode = false;
                break;
            }
            case Amino::ina_: {
                bound_strand.insert(pos+1, 1, 'A');
                opposite_strand.insert(pos+1, 1, copy_mode ? 'T' : ' ');
                pos += 1;
                break;
            }
            case Amino::inc_: {
                bound_strand.insert(pos+1, 1, 'C');
                opposite_strand.insert(pos+1, 1, copy_mode ? 'G' : ' ');
                pos += 1;
                break;
            }
            case Amino::ing_: {
                bound_strand.insert(pos+1, 1, 'G');
                opposite_strand.insert(pos+1, 1, copy_mode ? 'C' : ' ');
                pos += 1;
                break;
            }
            case Amino::int_: {
                bound_strand.insert(pos+1, 1, 'T');
                opposite_strand.insert(pos+1, 1, copy_mode ? 'A' : ' ');
                pos += 1;
                break;
            }
            case Amino::rpy_: {
                while (true) {
                    pos += 1;
                    if (pos == bound_strand.length() || bound_strand[pos] == ' ') {
                        finished = true;
                        break;
                    } else if (copy_mode) {
                        opposite_strand[pos] = complementary_base(bound_strand[pos]);
                    }
                    if (is_pyrimidine(bound_strand[pos])) {
                        break;
                    }
                }
                break;
            }
            case Amino::rpu_: {
                while (true) {
                    pos += 1;
                    if (pos == bound_strand.length() || bound_strand[pos] == ' ') {
                        finished = true;
                        break;
                    } else if (copy_mode) {
                        opposite_strand[pos] = complementary_base(bound_strand[pos]);
                    }
                    if (is_purine(bound_strand[pos])) {
                        break;
                    }
                }
                break;
            }
            case Amino::lpy_: {
                while (true) {
                    pos -= 1;
                    if (pos == -1 || bound_strand[pos] == ' ') {
                        finished = true;
                        break;
                    } else if (copy_mode) {
                        opposite_strand[pos] = complementary_base(bound_strand[pos]);
                    }
                    if (is_pyrimidine(bound_strand[pos])) {
                        break;
                    }
                }
                break;
            }
            case Amino::lpu_: {
                while (true) {
                    pos -= 1;
                    if (pos == -1 || bound_strand[pos] == ' ') {
                        finished = true;
                        break;
                    } else if (copy_mode) {
                        opposite_strand[pos] = complementary_base(bound_strand[pos]);
                    }
                    if (is_purine(bound_strand[pos])) {
                        break;
                    }
                }
                break;
            }
        }
    }
    maybe_add_to_pool(bound_strand);
    maybe_add_to_pool(reverse(opposite_strand));
    return pool;
}
