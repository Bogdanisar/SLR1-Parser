#include <bits/stdc++.h>

#define pv(x) std::cerr<<#x<<" = "<<(x)<<"; ";std::cerr.flush()
#define pn std::cerr<<std::endl

using namespace std;

using ll = long long;
using ull = unsigned long long;
using uint = unsigned int;
using ld = long double;
using pii = pair<int,int>;
using pll = pair<ll,ll>;
using pld = pair<ld, ld>;

// g++ main.cpp -Wall -Wextra -o main.exe && ./main.exe




const int NMax = 1e5 + 5;

const char LAMBDA = '_';
const char END_SYMBOL = '#';
const char NEW_START_SYMBOL = '$';

struct Production {
    int id;
    char lhs;
    string rhs;

    friend ostream& operator <<(ostream& out, const Production& p) {
        string rhs = (p.rhs == "") ? string(1, LAMBDA) : p.rhs;
        out << p.id << ": " << p.lhs << " -> " << rhs;
        return out;
    }
};

struct LR0Item {
    int idOfProduction;
    char lhs;
    string beforeDot;
    string afterDot;

    friend bool operator <(const LR0Item& a, const LR0Item& other) {
        return tie(a.idOfProduction, a.lhs, a.beforeDot, a.afterDot) < tie(other.idOfProduction, other.lhs, other.beforeDot, other.afterDot);
    }

    friend bool operator ==(const LR0Item& a, const LR0Item& other) {
        return tie(a.idOfProduction, a.lhs, a.beforeDot, a.afterDot) == tie(other.idOfProduction, other.lhs, other.beforeDot, other.afterDot);
    }

    friend ostream& operator <<(ostream& out, const LR0Item& item) {
        return out << item.idOfProduction << ' ' << item.lhs << " -> " << item.beforeDot << "." << item.afterDot;
    }
};
using DFAState = set<LR0Item>;

enum class ACTION_TYPE {
    SHIFT, REDUCE, ACCEPT, ERROR
};

struct Action {
    ACTION_TYPE type;
    int id;

    Action() {
        id = -1;
        type = ACTION_TYPE::ERROR;
    }

    friend ostream& operator <<(ostream& out, const Action& act) {
        if (act.type == ACTION_TYPE::SHIFT) {
            out << "shift " << act.id;
        }
        else if (act.type == ACTION_TYPE::REDUCE) {
            out << "reduce " << act.id;
        }
        else if (act.type == ACTION_TYPE::ACCEPT) {
            out << "accept";
        }
        else {
            out << "ERROR";
        }

        return out;
    }
};


ifstream in("input.in");
ofstream out("output.out");

int N;
char S;
vector<Production> allProd;
set<char> nonTerminals, terminals;
map<char, vector<Production>> prod;
map<char, set<string>> first, follow;
map< DFAState, int > DFAStateToId;
map< int, DFAState > idToDFAState;
// DFATransition[5]['S'] = State in the DFA that we get from state 5 with symbol 'S'
map< int, map<char, int> > DFATransition;

map< int, map<char, Action> > actionTable;
map< int, map<char, int> >    gotoTable;



bool isUpper(char c) {
    return 'A' <= c && c <= 'Z';
}

bool isNonTerminal(char c) {
    return isUpper(c) || c == NEW_START_SYMBOL;
}

bool hasNonTerminal(string str) {
    for (char c : str) {
        if (isNonTerminal(c)) {
            return true;
        }
    }

    return false;
}

bool isTerminal(char c) {
    return !isNonTerminal(c);
}

string removeSubstring(string str, const string& sub) {
    size_t index = 0;
    while (true) {
        /* Locate the substring to replace. */
        index = str.find(sub, index);
        if (index == std::string::npos) {
            break;
        }

        /* Make the replacement. */
        str.replace(index, sub.length(), "");
    }
    
    return str;
}

string removeLambda(string str) {
    return removeSubstring(str, string(1, LAMBDA));
}

void addNonTerminalsAndTerminals(string str) {
    for (char c : str) {
        if (isNonTerminal(c)) {
            nonTerminals.insert(c);
        }
        else {
            terminals.insert(c);
        }
    }
}

void addNonTerminalsAndTerminals(char c) {
    addNonTerminalsAndTerminals(string(1, c));
}


set<string> getFirst1Of(const string& str, map<char, set<string>>& functionOfLast) {
    set<string> ret;

    bool allNullable = true;
    unsigned i = 0;
    for (const char& c : str) {
        set<string> currSet;
        if (i < str.size() - 1) {
            currSet = first[c];
        }
        else {
            currSet = functionOfLast[c];
        }

        for (string f : currSet) {
            if (f != "") {
                ret.insert(f);
            }
        }

        bool currNotNullabe = (currSet.count("") == 0);
        if (currNotNullabe) { // we only keep going if this symbol is nullable
            allNullable = false;
            break;
        }

        ++i;
    }

    if (allNullable) {
        ret.insert("");
    }

    return ret;
}

template<typename T>
bool addSetToSet(set<T>& s, const set<T>& add) {
    bool change = false;

    for (const T& e : add) {
        if (s.count(e) == 0) {
            s.insert(e);
            change = true;
        }
    }

    return change;
}


void computeFirst() {
    for (char t : terminals) {
        first[t].insert( string(1,t) );
    }

    for (Production p : allProd) {
        if (hasNonTerminal(p.rhs) == false) {
            first[p.lhs].insert( p.rhs.substr(0, 1) );
        }
    }

    bool change = false;
    do {
        change = false;

        for (Production p : allProd) {
            if (hasNonTerminal(p.rhs) == false) {
                continue;
            }

            set<string> addSet = getFirst1Of(p.rhs, first);
            if ( addSetToSet(first[p.lhs], addSet) ) {
                change = true;
            }
        }
    }
    while (change);
}


void computeFollow() {
    follow[S].insert( string(1, END_SYMBOL) );

    bool change;
    do {
        change = false;

        for (Production p : allProd) {
            for (unsigned i = 0; i < p.rhs.size(); ++i) {
                char s = p.rhs[i];

                if (isNonTerminal(s)) {
                    string suffix = p.rhs.substr(i + 1);

                    set<string> addSet = getFirst1Of(suffix + string(1, p.lhs), follow);
                    if ( addSetToSet(follow[s], addSet) ) {
                        change = true;
                    }
                }
            }
        }
    }
    while (change);
}

void printFirstSets(ostream& out) {
    string sep = "=============== Printing First(symbol) ===============";
    out << sep << '\n';

    vector<char> allSymbols(terminals.begin(), terminals.end());
    allSymbols.insert(allSymbols.end(), nonTerminals.begin(), nonTerminals.end());
    
    for (char s : allSymbols) {
        out << "First( '" << s << "' ):\n";
        for (string f : first[s]) {
            if (f == "") {
                f = string(1, LAMBDA);
            }

            out << "'" << f << "', ";
        }
        out << '\n';
    }

    out << sep << "\n\n";
}


void printFollowSets(ostream& out) {
    string sep = "=============== Printing Follow(nonTerminal) ===============";
    out << sep << '\n';
    
    for (char s : nonTerminals) {
        out << "Follow( '" << s << "' ):\n";
        for (string f : follow[s]) {
            if (f == "") {
                f = string(1, LAMBDA);
            }

            out << "'" << f << "', ";
        }
        out << '\n';
    }

    out << sep << "\n\n";
}





set<LR0Item> getClosure(set<LR0Item> init) {
    queue<LR0Item> unmarked;
    set<LR0Item> ret = init;

    for (auto& item : init) {
        unmarked.push(item);
    }
    
    while (unmarked.size()) {
        auto curr = unmarked.front(); unmarked.pop();

        if (curr.afterDot == "") {
            continue;
        }

        char symbol = curr.afterDot[0];
        if (isNonTerminal(symbol)) {
            for (Production p : prod[symbol]) {
                LR0Item lr;
                lr.idOfProduction = p.id;
                lr.lhs = p.lhs;
                lr.beforeDot = "";
                lr.afterDot = p.rhs;

                if (ret.count(lr) == 0) {
                    ret.insert(lr);
                    unmarked.push(lr);
                }
            }
        }
    }
    
    return ret;
}

DFAState nextState(DFAState state, char symbol) {
    DFAState nxt;
    for (LR0Item item : state) {
        if ( item.afterDot.substr(0, 1) == string(1, symbol) ) {
            LR0Item newItem;
            newItem.idOfProduction = item.idOfProduction;
            newItem.lhs = item.lhs;
            newItem.beforeDot = item.beforeDot + string(1, symbol);
            newItem.afterDot = item.afterDot.substr(1);

            nxt.insert(newItem);
        }
    }

    return getClosure(nxt);
}


void buildDFATransitionTable() {
    LR0Item addedItem;
    addedItem.idOfProduction = 0;
    addedItem.lhs = NEW_START_SYMBOL;
    addedItem.beforeDot = "";
    addedItem.afterDot = string(1, S);

    DFAState state1 = getClosure({addedItem});
    int stateCounter = 1;
    idToDFAState[stateCounter] = state1;
    DFAStateToId[state1] = stateCounter++;

    queue<DFAState> unmarked;
    unmarked.push(state1);
    while (unmarked.size()) {
        DFAState curr = unmarked.front(); unmarked.pop();

        set<char> allSymbols = terminals;
        addSetToSet(allSymbols, nonTerminals);
        for (const char& symbol : allSymbols) {
            DFAState nxt = nextState(curr, symbol);

            if (nxt == DFAState()) {
                continue;
            }

            if (DFAStateToId[nxt] == 0) {
                idToDFAState[stateCounter] = nxt;
                DFAStateToId[nxt] = stateCounter++;
                unmarked.push(nxt);
            }

            int currId = DFAStateToId[curr];
            int nxtId = DFAStateToId[nxt];
            DFATransition[currId][symbol] = nxtId;
        }
    }
}

void printDFAStates(ostream& out) {
    for (auto p : idToDFAState) {
        int id = p.first;
        DFAState& state = p.second;

        out << "state" << id << '\n';
        for (LR0Item item : state) {
            out << item << '\n';
        }
        out << "\n\n";
    }
    out << "\n\n";
}

void printDFATransitions(ostream& out) {
    for (auto p1 : idToDFAState) {
        int id = p1.first;
        for (auto p2 : DFATransition[id]) {
            char symbol = p2.first;
            int nxtId = p2.second;

            out << "delta[" << id << "][" << symbol << "] = " << nxtId << '\n';
        }

        if (DFATransition[id].size() == 0) {
            out << "delta[" << id << "][?] = nothing\n";
        }
    }
    out << '\n';
}









bool addActionAndCheckForFailure(int currId, char symbol, Action act) {
    if (actionTable[currId].count(symbol) > 0) {
        out << "Found two actions for transition from state with id: " << currId << " with symbol " << symbol << ":\n";
        out << actionTable[currId][symbol] << '\n';
        out << "conflicts with:\n";
        out << act << '\n';
        return true;
    }
    else {
        actionTable[currId][symbol] = act;
        return false;
    }
}


bool buildActionAndGotoTables() {
    for (auto p : idToDFAState) {
        int currStateId = p.first;
        DFAState& currState = p.second;

        for (LR0Item item : currState) {
            if (item.afterDot != "" && isTerminal(item.afterDot[0])) {
                assert(DFATransition[currStateId].count(item.afterDot[0]) > 0);

                Action act;
                act.type = ACTION_TYPE::SHIFT;
                act.id = DFATransition[currStateId][item.afterDot[0]];

                bool didFail = addActionAndCheckForFailure(currStateId, item.afterDot[0], act);
                if (didFail) {
                    return false;
                }
            }
            else if (item.idOfProduction != 0 && item.afterDot == "") {
                Action act;
                act.type = ACTION_TYPE::REDUCE;
                act.id = item.idOfProduction;
                char lhs = allProd[act.id].lhs;

                for (string str : follow[lhs]) {
                    if (str == "") {
                        continue;
                    }

                    bool didFail = addActionAndCheckForFailure(currStateId, str[0], act);
                    if (didFail) {
                        return false;
                    }
                }
            }
            else if (item.idOfProduction == 0 && item.afterDot == "") {
                Action act;
                act.type = ACTION_TYPE::ACCEPT;

                bool didFail = addActionAndCheckForFailure(currStateId, END_SYMBOL, act);
                if (didFail) {
                    return false;
                }
            }
        }

        for (char nt : nonTerminals) {
            if (DFATransition[currStateId].count(nt) > 0) {
                gotoTable[currStateId][nt] = DFATransition[currStateId][nt];
            }
        }
    }

    return true;
}

void printActionTable() {
    for (auto p : idToDFAState) {
        int currStateId = p.first;

        for (char t : terminals) {
            out << "action[" << currStateId << "][" << t << "] = " << actionTable[currStateId][t] << '\n';
        }
    }
    out << "\n\n";
}

void printGotoTable() {
    for (auto p : idToDFAState) {
        int currStateId = p.first;

        for (char nt : nonTerminals) {
            out << "goto[" << currStateId << "][" << nt << "] = " << gotoTable[currStateId][nt] << '\n';
        }
    }
    out << "\n\n";
}







pair<bool, vector<int>> analyzeWord(string w) {
    out << "Analyzing word " << w << ":\n";

    w += END_SYMBOL;

    vector<int> stk;
    vector<int> productions;
    stk.push_back(1); // initial DFA state;
    while (true) {
        out << "Stack: ";
        for (int q : stk) {
            out << q << ' ';
        }
        out << "w: " << w << '\n';
        // out << "Prod: ";
        // out.flush();
        // for (int p : productions) {
        //     out << allProd[p] << endl;
        // }
        // out << endl;

        int currState = stk.back();
        char currSymbol = w[0];

        Action act = actionTable[currState][currSymbol];
        if (act.type == ACTION_TYPE::ACCEPT) {
            reverse(productions.begin(), productions.end());
            return {true, productions};
        }
        else if (act.type == ACTION_TYPE::ERROR) {
            reverse(productions.begin(), productions.end());
            return {false, productions};
        }
        else if (act.type == ACTION_TYPE::SHIFT) {
            stk.push_back(act.id);
            w = w.substr(1);
        }
        else if (act.type == ACTION_TYPE::REDUCE) {
            Production p = allProd[act.id];
            size_t lenOfProd = p.rhs.size();
            assert(stk.size() >= lenOfProd + 1);

            for (unsigned c = 0; c < lenOfProd; ++c) {
                stk.pop_back();
            }

            if (gotoTable[stk.back()][p.lhs] == 0) { // no transition found
                reverse(productions.begin(), productions.end());
                return {false, productions};
            }
            stk.push_back(gotoTable[stk.back()][p.lhs]);
            productions.push_back(p.id);
        }
    }

    assert(false);
}








int main() {
    assert(string("").substr(0, 1) == "");
    assert(string("a").substr(0, 0) == "");
    assert(removeSubstring("alabalaportocaaaaala", "a") == "lblportocl");
    assert(removeSubstring("alabalaportocaaaaala", "aa") == "alabalaportocala");
    assert(removeSubstring("alabalaportocaaaaaala", "aa") == "alabalaportocla");

    in >> N >> S;

    Production initProd;

    initProd.id = 0;
    initProd.lhs = NEW_START_SYMBOL;
    initProd.rhs = string(1, S);
    allProd.push_back(initProd);
    prod[initProd.lhs].push_back(initProd);
    addNonTerminalsAndTerminals(NEW_START_SYMBOL);
    addNonTerminalsAndTerminals(END_SYMBOL);


    int counter = 0;
    for (int i = 0; i < N; ++i) {
        Production p;
        p.id = ++counter;
        in >> p.lhs >> p.rhs;
        p.rhs = removeLambda(p.rhs);

        assert(isNonTerminal(p.lhs));
        assert(set<char>(p.rhs.begin(), p.rhs.end()).count(LAMBDA) == 0);

        allProd.push_back(p);
        prod[p.lhs].push_back(p);

        addNonTerminalsAndTerminals(p.lhs);
        addNonTerminalsAndTerminals(p.rhs);
    }


    computeFirst();
    printFirstSets(out);

    computeFollow();
    printFollowSets(out);
    
    buildDFATransitionTable();
    printDFAStates(out);
    printDFATransitions(out);

    bool success = buildActionAndGotoTables();
    if (!success) {
        out << "Grammar is not SLR(1)!\n";
        return -1;
    }

    out << "Grammer is SLR(1)!\n";
    printActionTable();
    printGotoTable();

    int nWords;
    in >> nWords;
    for (int c = 0; c < nWords; ++c) {
        string w;
        in >> w;
        string newWord = removeLambda(w);

        auto p = analyzeWord(newWord);
        bool inGrammar = p.first;
        vector<int> productions = p.second;
        if (inGrammar) {
            out << "Word " << w << " is in the grammar. Productions:\n";
            for (int prodIndex : productions) {
                out << allProd[prodIndex] << '\n';
            }
            out << '\n';
        }
        else {
            out << "Word " << w << " isn't in the grammar. \n\n";
        }
    }

    return 0;
}