#include "dna.h"
#include <cassert>
#include <set>
#include <vector>

void page_505()
{
    Strand s1("GGGG");
    Strand s2("ATTACCA");
    Strand s3("CATCATCATCAT");
}

void page_506()
{
    Enzyme e1({Amino::del_, Amino::mvr_, Amino::int_});
    assert(e1.binding_preference() == 'A');
    Strand s1("ACA");
    assert(s1.count_binding_sites('A') == 2);
    assert(e1.act_upon(Strand("ACA"), 0) == std::vector<Strand>{Strand("CAT")}); // bind to the left 'A'
    assert(e1.act_upon(Strand("ACA"), 1) == std::vector<Strand>{Strand("AC")}); // bind to the right 'A'
}

void page_507()
{
    Enzyme e1({Amino::rpy_, Amino::cop_, Amino::rpu_, Amino::cut_});
    assert(e1.binding_preference() == 'A');
    Strand s1("CAAAGAGAATCCTCTTTGAT");
    assert(s1.count_binding_sites(e1.binding_preference()) == 7);
    auto strands = e1.act_upon(s1, 1);
    assert((std::set<Strand>(strands.begin(), strands.end()) == std::set<Strand>{
        Strand("AT"),
        Strand("CAAAGAGGA"),
        Strand("CAAAGAGAATCCTCTTTG"),
    }));
}

void page_508()
{
    Enzyme e1({Amino::rpu_, Amino::inc_, Amino::cop_, Amino::mvr_, Amino::mvl_, Amino::swi_, Amino::lpu_, Amino::int_});
    assert(e1.binding_preference() != 'G');  // Hofstadter got this one wrong
    assert(e1.binding_preference() == 'T');
    Strand s1("TAGATCCAGTCCATCGA");
    assert(s1.count_binding_sites(e1.binding_preference()) == 4);
    auto strands = e1.act_upon(s1, 2);
    assert((std::set<Strand>(strands.begin(), strands.end()) == std::set<Strand>{
        Strand("ATG"),
        Strand("TAGATCCAGTCCACATCGA"),
    }));
}

void page_510()
{
    Strand s1("TAGATCCAGTCCACATCGA");
    auto v1 = s1.translate();
    assert((v1 == std::vector<Enzyme>{
        Enzyme({Amino::rpy_, Amino::ina_, Amino::rpu_, Amino::mvr_, Amino::int_, Amino::mvl_, Amino::cut_, Amino::swi_, Amino::cop_})
    }));
}

void page_511()
{
    Strand s1("CGGATACTAAACCGA");
    auto v1 = s1.translate();
    assert((std::set<Enzyme>(v1.begin(), v1.end()) == std::set<Enzyme>{
        Enzyme({Amino::cop_, Amino::ina_, Amino::rpy_, Amino::off_}),
        Enzyme({Amino::cut_, Amino::cop_}),
    }));
    assert((Strand("CAAG").translate() == std::vector<Enzyme>{
        Enzyme({Amino::mvr_, Amino::del_}),
    }));
}

void online()
{
    // Seen on David Fifield's page https://www.bamsoftware.com/hacks/geb/index.html
    // which credits its discovery to a now-lost(?) Scheme implementation by David Boozer.
    Strand selfrep("CAAAAAAACGTTTTTTTG");
    auto v1 = selfrep.translate();
    assert(v1.size() == 1);
    assert((v1[0].act_upon(selfrep, 0) == std::vector<Strand>{ selfrep, selfrep }));
}

int main()
{
    page_505();
    page_506();
    page_507();
    page_508();
    page_510();
    page_511();
}
