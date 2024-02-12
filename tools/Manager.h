// #include <bits/stdc++.h>

#include "report.h"

#include <stdlib.h>
#include <string>
#include <iostream>
#include <istream>
#include <fstream>
#include <unistd.h>
#include <vector>
#include <tuple>
#include <algorithm>
#include <list>
#include <unordered_map>
#include <map>
#include <set>
#include <utility>
#include <queue>

#include <stdio.h>
#include <unordered_set>

#define endl '\n'

using namespace std;

/*
  This constant represents the negation token used throughout the file.
*/
const char negation_token = '~';

bool unsat_derived = false;

/*
   This struct stores information for a single term.

   - [coeff] is an integer representing the coefficient of the term.
   - [var] is a string representing the variable the term refers to.
   - [neg] is a bool representing whether the term is negated
*/
struct term
{
  int coeff;
  int var;
  bool neg;

  term(int coeff_, int var_, bool neg_)
  {
    coeff = coeff_;
    var = var_;
    neg = neg_;
  }

  string output_term();
};

struct VariableManager
{

  unordered_map<string, int> assigned; // each underlying to the var int
  unordered_map<int, string> r_assigned;
  int nxt = 1;

  int get_variable(string vname)
  {
    if (assigned.find(vname) == assigned.end())
    {
      assigned[vname] = nxt;
      r_assigned[nxt] = vname;
      nxt++;
    }
    return assigned[vname];
  }

  term get_term(string r)
  { // always returns term with coeff = 1! set coeff after
    if (r[0] == negation_token)
    {
      r = r.substr(1, string::npos);
      return term(1, get_variable(r), true);
    }
    else
    {
      return term(1, get_variable(r), false);
    }
  }

  term get_term_with_coeff(string r, int coeff)
  {
    term m = get_term(r);
    m.coeff = coeff;
    return m;
  }

  string get_string(int var, bool neg)
  {
    string m = r_assigned[var];
    if (neg)
    {
      string e = "";
      e += negation_token;
      e += m;
      m = e;
    }
    return m;
  }

} vm;

string term::output_term()
{
  string ret = "";
  ret += to_string(coeff);
  ret += " ";
  ret += vm.get_string(var, neg);
  return ret;
  //    cout << coeff << ' ';
  //    if (neg) cout << negation_token;
  //    cout << var;
}

string basic_literal(string var)
{
  if (var[0] == negation_token)
    return var.substr(1, string::npos);
  return var;
}

/*
  Comparator function to sort terms in descending order of coefficient.
*/
bool compare_terms_by_coeff(term &a, term &b)
{
  return a.coeff > b.coeff;
}

/*
  This struct stores information about a clause which is not constrained.

  The only constraints that must be followed when using this structure are:
  (1) All constraints must exclusively be in >= form.
  (2) All constraints must have at most one occurrence of any variable.

  All other constraints are not enforced at this point. The intention of this
  structure is to read in from (well-formed) input and immediately pass this
  to the internal algorithms, which will convert into the required internal
  storage struct for you.

  - [terms] is a list of term structs (defined above)
  - [rhs] is an integer representing the value of the right-hand-side
*/
struct input_clause
{
  list<term> terms;
  int rhs;

  input_clause() {}

  input_clause(list<term> l, int r)
  {
    terms = l;
    rhs = r;
  }
};

/*
  This struct is identical to the struct above, but with the key difference
  that invariants critical to our algorithm are maintained throughout the
  lifetime of this struct.

  Apart from the constraints in the [input_clause] form above, two additional
  constraints are enforced:
  (1) All terms are stored in descending order of magnitude (coefficients)
  (2) All coefficients must be strictly positive: if negative, coefficient
  normalisation is applied, and if zero, the term can be dropped.

  - [terms] is a list of term structs (defined above)
  - [rhs] is an integer representing the value of the right-hand-side
*/
struct clause
{

  list<term> terms;
  int rhs;

  clause() {}

  /* Constructor to convert from an [input_clause] to a [clause]. */
  clause(input_clause derive_from)
  {
    vector<term> term_list;
    rhs = derive_from.rhs;
    for (auto &original_term : derive_from.terms)
    {
      if (original_term.coeff == 0)
      {
        continue;
      }
      else if (original_term.coeff < 0)
      {
        rhs -= original_term.coeff;
        term_list.push_back(
            term(-original_term.coeff,
                 original_term.var,
                 !original_term.neg));
      }
      else
      {
        term_list.push_back(original_term);
      }
    }
    sort(term_list.begin(), term_list.end(), compare_terms_by_coeff);
    for (auto &term : term_list)
    {
      terms.push_back(term);
    }
  }

  string output_clause()
  {
    string s = "";
    for (auto it = terms.begin(); it != terms.end(); it++)
    {
      s += it->output_term();
      s += " ";
      // cout << ' ';
    }
    s += ">= ";
    s += to_string(rhs);
    //    cout << ">= " << rhs;
    return s;
  }
};

clause clause_sum(clause &a, clause &b)
{ // !x = 1 - x
  input_clause res;
  res.rhs = a.rhs + b.rhs;
  unordered_map<int, int> sms;
  for (auto &term : a.terms)
  {
    if (term.neg)
    {
      sms[term.var] -= term.coeff;
      res.rhs -= term.coeff;
    }
    else
    {
      sms[term.var] += term.coeff;
    }
  }
  for (auto &term : b.terms)
  {
    if (term.neg)
    {
      sms[term.var] -= term.coeff;
      res.rhs -= term.coeff;
    }
    else
    {
      sms[term.var] += term.coeff;
    }
  }
  for (auto curr_term : sms)
  {
    res.terms.push_back(term(curr_term.second, curr_term.first, false));
  }
  clause result(res);
  return result;
}

clause clause_prod(clause &a, int k)
{
  clause r;
  r.rhs = a.rhs * k;
  for (auto &curr_term : a.terms)
  {
    r.terms.push_back(term(curr_term.coeff * k, curr_term.var, curr_term.neg));
  }
  return r;
}

int ceil_div(int n, int k)
{
  return (n + k - 1) / k;
}

clause clause_div(clause &a, int k)
{
  clause r;
  r.rhs = ceil_div(a.rhs, k);
  for (auto &curr_term : a.terms)
  {
    r.terms.push_back(term(ceil_div(curr_term.coeff, k), curr_term.var, curr_term.neg));
  }
  return r;
}

clause clause_sat(clause &a)
{
  clause r;
  r.rhs = a.rhs;
  for (auto &curr_term : a.terms)
  {
    r.terms.push_back(term(min(curr_term.coeff, r.rhs), curr_term.var, curr_term.neg));
  }
  return r;
}

struct clause_response
{

  clause c;
  int hints[2];

  void output()
  {
    string s = c.output_clause();
    cout << s;
    cout << " <with-hints> " << hints[0] << ' ' << hints[1] << endl;
  }
};

struct final_clause
{
  clause c;
  int hints[2];
  char clause_type;
};

struct rpn_token
{
  bool is_numeric;

  union data
  {
    int id_value;
    char op_type;
  };

  data d;

  rpn_token(int x)
  {
    is_numeric = true;
    d.id_value = x;
  }

  rpn_token(char x)
  {
    is_numeric = false;
    d.op_type = x;
  }
};

struct rpn_input
{
  list<rpn_token> tokens;
  bool one_indexed;

  rpn_input(bool one_index = true)
  {
    one_indexed = one_index;
  }
  rpn_input(list<rpn_token> token_list, bool one_index = true)
  {
    one_indexed = one_index;
    tokens = token_list;
  }

  void output()
  {
    for (auto x : tokens)
    {
      if (x.is_numeric)
        cout << x.d.id_value << ' ';
      else
        cout << x.d.op_type << ' ';
    }
  }
};

struct rpn_token_comp
{
  bool operator()(const rpn_token a, const rpn_token b) const
  {
    if (a.is_numeric != b.is_numeric)
      return a.is_numeric;
    if (a.is_numeric)
      return a.d.id_value < b.d.id_value;
    return a.d.op_type < b.d.op_type;
  }
};

struct rpn_trie
{

  struct rpn_trie_node
  {
    int terminal_clause = -1;
    map<rpn_token, rpn_trie_node *, rpn_token_comp> children;

    rpn_trie_node()
    {
      terminal_clause = -1;
    }

    rpn_trie_node *get_child(rpn_token r)
    {
      if (children.find(r) != children.end())
        return children[r];
      return children[r] = (new rpn_trie_node());
    }

    void output(int t = 0)
    {
      for (int i = 0; i < t; i++)
        cout << ' ';
      cout << "node: " << terminal_clause << endl;
      for (auto f : children)
      {
        f.second->output(t + 1);
      }
    }
  };

  rpn_trie_node *root = NULL;

  rpn_trie()
  {
    root = new rpn_trie_node();
  }

  void insert(rpn_input inp, int clause_number)
  {
    rpn_trie_node *curr = root;
    for (auto token : inp.tokens)
    {
      curr = curr->get_child(token);
    }
    curr->terminal_clause = clause_number;
  }

  void output()
  {
    cout << "--- ostart ---" << endl;
    root->output();
    cout << "---  oend  ---" << endl;
  }

  rpn_input simplify_clause(rpn_input r)
  {
    int mx = 0;
    int wh = -1;
    auto x = r.tokens.begin();
    rpn_trie_node *curr = root;
    for (int i = 0; i < r.tokens.size(); i++)
    {
      curr = curr->get_child(*x);
      x++;
      if (curr->terminal_clause != -1)
      {
        mx = i + 1;
        wh = curr->terminal_clause;
      }
    }
    if (wh == -1)
      return r; // no simplification
    // the first mx items can be replaced with wh
    rpn_input updated(r.one_indexed);
    updated.tokens.push_back(wh + r.one_indexed);
    int cnum = 0;
    for (auto token : r.tokens)
    {
      cnum++;
      if (cnum <= mx)
        continue;
      updated.tokens.push_back(token);
    }
    return updated;
  }
};

clause negate_clause(clause input)
{
  clause new_clause;
  new_clause.rhs = -input.rhs + 1;
  for (auto &input_term : input.terms)
  {
    new_clause.terms.push_back(term(input_term.coeff, input_term.var, !input_term.neg));
    new_clause.rhs += input_term.coeff;
  }
  return new_clause;
}

namespace unit_propagation
{

  const int UNPROP = 1 << 30;

  vector<tuple<int, int, int>> derive(vector<clause> clauses, int num_vars)
  {

    bool new_format = true;
    vector<tuple<int, int, int>> new_format_response;

    /* cout << "DERIVE CLAUSE HISTORY *----" << endl; */
    /* for (auto c : clauses) { */
    /*   cout << c.output_clause() << endl; */
    /* }  */
    /* cout << "*----" << endl; */

    int n = clauses.size();
    new_format_response.clear();

    vector<int> latest_version_ids; // for each clause, latest version of that clause is the only one we must consider

    vector<pair<int, list<term>::iterator>> occs_array[num_vars + 1]; // TODO: nvars

    // unordered_map<int, vector<pair<int, list<term>::iterator>>> occs; // for each variable, every ORIGINAL clause it occurs in
    int clause_lhs_sum[n];

    bool seenvar[num_vars + 1];
    //    unordered_map<int, bool> seenvar;

    for (int i = 0; i < n; i++)
    {
      clause_lhs_sum[i] = 0;
      auto it = clauses[i].terms.begin();
      for (auto term : clauses[i].terms)
      {
        occs_array[term.var].push_back({i, it});
        // occs[term.var].push_back({i, it});
        clause_lhs_sum[i] += term.coeff;
        assert(term.coeff >= 0);
        it++;
      }
    }

    for (int i = 0; i < n; i++)
    {
      latest_version_ids.push_back(i);
    }

    int current_slacks[n];
    for (int i = 0; i < n; i++)
    {
      current_slacks[i] = clause_lhs_sum[i] - clauses[i].rhs;
    }

    int current_propagation_factor[n]; // for each original clause, it is (slack - maxcoeff) of unsimplified items
    for (int i = 0; i < n; i++)
    {
      current_propagation_factor[i] = current_slacks[i];
      if (clauses[i].terms.empty())
        current_propagation_factor[i] = UNPROP; // if no terms can be propagated
      else
        current_propagation_factor[i] -= clauses[i].terms.front().coeff;
    }

    set<pair<int, int>> propagation_order; // {slack - maxcoeff, clause_id}
    for (int i = 0; i < n; i++)
    {
      propagation_order.insert({current_propagation_factor[i], i});
    }

    vector<pair<int, bool>> propagated;

    stack<pair<int, pair<bool, int>>> to_propagate; // list of things pending propagation
    // var, whether negated, what clause it came from
    stack<int> prop_counts;
    // parallel queue to store number of pending propagations for the next item

    int last_version[n];
    for (int i = 0; i < n; i++)
    {
      last_version[i] = i;
    }

    int next_assignable = n;
    vector<clause_response> responses;
    bool unsat_breaker = false;

    vector<tuple<int, int, int>> propagations;
    int unsat_clause = -1;

    while (!unsat_breaker)
    {

      // cout << "_---START" << endl;
      // for (int i=0; i<n; i++) {
      // 	clauses[i].output_clause(); cout << endl;
      // }
      // cout << "_---END" << endl;

      if (!to_propagate.empty())
      {
        // pick something to propagate
        // propagate it
        // reduce all clauses
        // did something become unsat?

        // improvement: reduce only as many clauses as necessary
        bool new_item = false;
        while (!to_propagate.empty())
        {
          if (prop_counts.top() == 0)
          {
            to_propagate.pop();
            prop_counts.pop();
          }
          else
          {
            break;
          }
        }

        if (to_propagate.empty())
          continue;
        auto prop = to_propagate.top(); // to_propagate.pop();
        prop_counts.top()--;

        int var = prop.first;
        bool neg = prop.second.first;
        int source_clause_id = prop.second.second;

        if (!seenvar[var])
          new_item = true;
        seenvar[var] = true;

        if (new_item)
          propagated.push_back({var, neg});

        //	cout << "PROP: " << var << ' ' << neg << endl;

        auto occ = occs_array[var][prop_counts.top()];
        // auto occ = occs[var][prop_counts.top()];
        {
          int clause_id = occ.first;
          list<term>::iterator pos = occ.second;
          assert(pos->var == var);
          if (pos->neg == neg)
          {
            clauses[clause_id].rhs -= pos->coeff;
          }
          clause_lhs_sum[clause_id] -= pos->coeff;
          current_slacks[clause_id] = clause_lhs_sum[clause_id] - clauses[clause_id].rhs;

          int old_prop_factor = current_propagation_factor[clause_id];

          // update prop factor

          clauses[clause_id].terms.erase(pos);

          if (clauses[clause_id].terms.empty())
          {
            current_propagation_factor[clause_id] = UNPROP;
          }
          else
          {
            current_propagation_factor[clause_id] = current_slacks[clause_id] - clauses[clause_id].terms.front().coeff;
          }

          propagation_order.erase(propagation_order.find({old_prop_factor, clause_id}));
          propagation_order.insert({current_propagation_factor[clause_id], clause_id});

          int previous_clause = last_version[clause_id];

          // make a copy of previous clause somehow?

          last_version[clause_id] = next_assignable;
          next_assignable++;

          if (current_slacks[clause_id] < 0)
          {
            // cout << "UNSAT!" << endl;
            unsat_breaker = true;
            unsat_clause = clause_id;
            break;
          }
        }
      }
      else
      {
        // find something to propagate, by checking the top-left corner of the box
        auto f = propagation_order.begin();
        auto val = *f;
        int curr_factor = val.first;
        int clause_id = val.second;
        assert(curr_factor < 0);                   // nothing can be propagated
        assert(!clauses[clause_id].terms.empty()); // something must be propagate-able
        auto prop_term = clauses[clause_id].terms.front();
        //	cout << "V: " << clause_id << ": " << prop_term.var << " " << prop_term.neg << endl;
        to_propagate.push({prop_term.var, {prop_term.neg, last_version[clause_id]}});

        prop_counts.push(occs_array[prop_term.var].size());
        // prop_counts.push(occs[prop_term.var].size());

        propagations.push_back({clause_id, prop_term.var, prop_term.neg});
      }
    }

    new_format_response = propagations;
    new_format_response.push_back({unsat_clause, -1, -1});
    return new_format_response;
  }

};

/*
  This struct co-ordinates the roles of every other aspect of the code. In
  some sense, this is the entry point to the code, and this is really the
  only way the library functions here should be interacted with. This
  does not handle IO, but can handle every algorithm discussed. It also
  compactly maintains the internal state necessary.

  Internally, all work is done in 0-indexed form. Only at the output step
  is everything converted to 1-indexing.
*/
struct Manager
{

  Manager() {}

  int num_vars;

  struct ClauseManager
  {

    vector<final_clause> clauses;
    int next_original_clause_id = 0;
    vector<int> original_id_to_new_id;
    vector<vector<tuple<int, int, int>>> current_new_format_items;
    int opt_id;

    ClauseManager()
    {
      next_original_clause_id = 0;
    }

    int add_clause(char clause_type, clause r, int hint1 = -1, int hint2 = -1)
    {
      final_clause c;
      c.clause_type = clause_type;
      c.c = r;
      c.hints[0] = hint1;
      c.hints[1] = hint2;
      int this_clause = clauses.size();
      clauses.push_back(c);
      return this_clause;
    }

    int get_next_original_clause_id()
    {
      next_original_clause_id++;
      return next_original_clause_id - 1;
    }

    int add_original_clause(char clause_type, clause r, int hint1 = -1, int hint2 = -1)
    {
      final_clause c;
      c.clause_type = clause_type;
      c.c = r;
      c.hints[0] = hint1;
      c.hints[1] = hint2;
      int this_clause = clauses.size();
      clauses.push_back(c);
      original_id_to_new_id.push_back(this_clause);
      get_next_original_clause_id();
      return this_clause;
    }

    void register_opt(clause r)
    {
      final_clause c;
      c.clause_type = 'i';
      c.c = r;
      c.hints[0] = -1;
      c.hints[1] = -1;
      clauses.push_back(c);
      opt_id = clauses.size() - 1;
    }
    void add_opt()
    {
      add_original_clause('a', clauses[opt_id].c, opt_id);
    }

    void ignore_original_clauses(int k)
    {
      while (k >= 0)
      {
        original_id_to_new_id.push_back(-1);
        k--;
      }
    }

    final_clause &clause_with_id(int id)
    {
      return clauses[id];
    }

    final_clause &clause_with_original_id(int id, bool one_indexed = false)
    {
      return clauses[original_id_to_new_id[id - one_indexed]];
    }

    int id_of_original_id(int id, bool one_indexed = false)
    {
      return original_id_to_new_id[id - one_indexed];
    }

    void edit_clause_hints(int clause_id, int hint1 = -1, int hint2 = -1)
    {
      clauses[clause_id].hints[0] = hint1;
      clauses[clause_id].hints[1] = hint2;
    }

    int add_new_format_lookup(vector<tuple<int, int, int>> items)
    {
      int id = current_new_format_items.size();
      current_new_format_items.push_back(items);
      return id;
    }

  } clauses;

  rpn_trie rpnt;

  Manager(int num_variables)
  {
    rpnt = rpn_trie();
    num_vars = num_variables;
  }

  void add_input(input_clause c)
  {
    //    cout << "ADD_INPUT" << endl;
    clause r(c);
    //    cout << r.output_clause() << endl;
    clauses.add_original_clause('i', r);
  }

  void add_rpn(rpn_input c)
  {

    //    cout << "===== BEFORE TRIE " << c.tokens.size() << endl;
    // every token is a node on the tree
    // operator nodes have dependencies
    // otherwise, each leaf is either a reference to a clause (in old numbering)
    //                         or a constant somehow

    auto c_init = c;

    c = rpnt.simplify_clause(c);

    //    cout << "===== AFTER TRIE " << c.tokens.size() << endl;

    //    cout << "c.output" << endl;
    //    c.output();

    //    cout << endl;

    vector<rpn_token> tokens(c.tokens.begin(), c.tokens.end());

    const int UNKNOWN = -1;
    const int CLAUSE = 1;
    const int CONSTANT = 2;

    int n = tokens.size();
    vector<int> stack_of_ids;
    vector<int> types;
    vector<vector<int>> dependencies;
    vector<int> values;

    for (int i = 0; i < n; i++)
    {
      if (tokens[i].is_numeric)
      {
        stack_of_ids.push_back(i);
        values.push_back(tokens[i].d.id_value);
        dependencies.push_back({});
        types.push_back(UNKNOWN); // we don't know the type of the current thing
      }
      else
      {
        values.push_back(-1);
        if (tokens[i].d.op_type == '+')
        {
          // top two are the sub-clauses
          int sub_2 = stack_of_ids.back();
          stack_of_ids.pop_back();
          int sub_1 = stack_of_ids.back();
          stack_of_ids.pop_back();
          types[sub_1] = types[sub_2] = CLAUSE;

          stack_of_ids.push_back(i);
          dependencies.push_back({sub_1, sub_2});
          types.push_back(CLAUSE);
        }
        else if (tokens[i].d.op_type == '*')
        {
          // top two are clause and constant respectively
          int sub_2 = stack_of_ids.back();
          stack_of_ids.pop_back();
          int sub_1 = stack_of_ids.back();
          stack_of_ids.pop_back();
          types[sub_1] = CLAUSE;
          types[sub_2] = CONSTANT;

          stack_of_ids.push_back(i);
          dependencies.push_back({sub_1, sub_2});
          types.push_back(CLAUSE);
        }
        else if (tokens[i].d.op_type == 'd')
        {
          // top two are clause and constant respectively
          int sub_2 = stack_of_ids.back();
          stack_of_ids.pop_back();
          int sub_1 = stack_of_ids.back();
          stack_of_ids.pop_back();
          types[sub_1] = CLAUSE;
          types[sub_2] = CONSTANT;

          stack_of_ids.push_back(i);
          dependencies.push_back({sub_1, sub_2});
          types.push_back(CLAUSE);
        }
        else if (tokens[i].d.op_type == 's')
        {
          // top one is clause
          int sub = stack_of_ids.back();
          stack_of_ids.pop_back();
          types[sub] = CLAUSE;

          stack_of_ids.push_back(i);
          dependencies.push_back({sub});
          types.push_back(CLAUSE);
        }
      }
    }

    types[n - 1] = CLAUSE;
    stack_of_ids.clear();

    vector<clause> real_contents; // for each ID, what are the actual contents?
    vector<int> source_hint;      // for each ID, where did the corresponding clause come from?

    for (int i = 0; i < n; i++)
    {
      if (tokens[i].is_numeric)
      {
        if (types[i] == CLAUSE)
        {
          int old_clause_id = tokens[i].d.id_value;
          real_contents.push_back(clauses.clause_with_original_id(old_clause_id, c.one_indexed).c);
          source_hint.push_back(clauses.id_of_original_id(old_clause_id, c.one_indexed));
        }
        else
        {
          real_contents.push_back(clause());
          source_hint.push_back(UNKNOWN);
        }
      }
      else
      {
        if (tokens[i].d.op_type == '+')
        {
          int a = dependencies[i][0], b = dependencies[i][1];
          clause summed = clause_sum(real_contents[a], real_contents[b]);
          real_contents.push_back(summed);
          int ncl = clauses.add_clause('a', summed, source_hint[a], source_hint[b]);
          source_hint.push_back(ncl);
        }
        else if (tokens[i].d.op_type == '*')
        {
          int a = dependencies[i][0], b = dependencies[i][1];
          clause product = clause_prod(real_contents[a], values[b]);
          real_contents.push_back(product);
          source_hint.push_back(source_hint[a]);
        }
        else if (tokens[i].d.op_type == 'd')
        {
          int a = dependencies[i][0], b = dependencies[i][1];
          clause quotient = clause_div(real_contents[a], values[b]);
          real_contents.push_back(quotient);
          int ncl = clauses.add_clause('a', quotient, source_hint[a]);
          source_hint.push_back(ncl);
        }
        else if (tokens[i].d.op_type == 's')
        {
          int a = dependencies[i][0];
          clause saturated = clause_sat(real_contents[a]);
          real_contents.push_back(saturated);
          source_hint.push_back(source_hint[a]);
        }
      }
    }

    int clause_id = clauses.next_original_clause_id;
    clauses.add_original_clause('a', real_contents.back(), source_hint.back());
    rpnt.insert(c_init, clause_id);
    //    rpnt.output();
  }

  void add_derive(input_clause target_clause, int num_vars)
  {
    if (unsat_derived)
    {
      return;
    }

    if ((target_clause.rhs == 1) && (target_clause.terms.size() == 0))
    {
      unsat_derived = true;
    }
    //    cout << "ADD_DERIVE" << endl;
    clause target(target_clause);
    //    cout << target.output_clause() << endl;
    clause negated_target = negate_clause(target);

    vector<clause> input_clauses;
    vector<int> relabellings;
    for (int i = 0; i < clauses.clauses.size(); i++)
    {
      if (clauses.clauses[i].clause_type == 'a' || clauses.clauses[i].clause_type == 'i' || clauses.clauses[i].clause_type == 'u')
      {
        if (i > 0 && clauses.clauses[i - 1].clause_type == 'a')
        {
          input_clauses.pop_back();
          relabellings.pop_back();
        }
        input_clauses.push_back(clauses.clauses[i].c);
        relabellings.push_back(i);
      }
    }

    int placed_point = clauses.add_original_clause('u', target);

    input_clauses.push_back(negated_target);
    relabellings.push_back(placed_point);

    auto result = unit_propagation::derive(input_clauses, num_vars);

    vector<tuple<int, int, int>> new_res;
    for (auto &[a, b, c] : result)
    {
      new_res.push_back(make_tuple(relabellings[a], b, c));
    }

    clauses.edit_clause_hints(placed_point, -2, clauses.add_new_format_lookup(new_res));
  }

  void ignore_original_clauses(int k)
  {
    clauses.ignore_original_clauses(k);
  }

  string printhint(int hint)
  {
    if (hint == -1)
      return "";
    if (hint < 0)
    {
      hint--;
    }
    else
    {
      hint++;
    }
    return to_string(hint);
  }

  void print_set(unordered_set<int> set)
  {
    cout << "{";
    for (auto it = set.begin(); it != set.end(); it++)
    {
      cout << to_string(*it) << " ";
    }
    cout << "}" << endl;
  }

void trimoutput(const string &filename = "") {
    double output_start = tod();
    int num_clauses = clauses.clauses.size();
    bool used[num_clauses];
    memset(used, false, sizeof used);

    used[num_clauses - 1] = true;
    
    for (int i=num_clauses-1; i>=0; i--) {
      if (!used[i]) continue;
      auto clause = clauses.clauses[i];
      if (clause.clause_type == 'u') {
        int id = clause.hints[1];
        int t = clauses.current_new_format_items[id].size();
        for (int i=0; i<t; i++) {
          auto &[cid, var, neg] = clauses.current_new_format_items[id][i];
          int dep_clause_id = cid;
          used[dep_clause_id] = true;
        }
      }
      else if (clause.clause_type == 'a') {
        int h1 = clause.hints[0], h2 = clause.hints[1];
        if (h1 != -1) used[h1] = true;
        if (h2 != -1) used[h2] = true;
      }
    }

    ofstream file(filename);
    assert(file.is_open());

    int renum[num_clauses];
    renum[-1] = -1;

    int ptr = 0;
    for (int i = 0; i < num_clauses; i++)
        {
          auto x = clauses.clauses[i];
          if (!used[i]) continue;
          renum[i] = ptr;
          file << x.clause_type << ' ';
          file << x.c.output_clause();
          file << " ; ";
          if (x.hints[0] == -2)
          {
            int id = x.hints[1];
            int t = clauses.current_new_format_items[id].size();
            for (int i = 0; i < t; i++)
            {
              auto &[cid, var, neg] = clauses.current_new_format_items[id][i];
              if (i + 1 == t) {
                auto hint = -1;
                if (cid != -1) hint = (renum[cid] == ptr) ? -renum[cid] : renum[cid];
                file << '[' << printhint(hint) << ']' << endl;
              }
              else {
                auto hint = -1;
                if (cid != -1) hint = (renum[cid] == ptr) ? -renum[cid] : renum[cid];
                file << '[' << printhint(hint) << ' ' << vm.get_string(var, neg) << "] ";
              }
            }
          }
          else
          {
            int h1 = x.hints[0], h2 = x.hints[1];
            if (h1 != -1) h1 = renum[h1];
            if (h2 != -1) h2 = renum[h2];
            file << printhint(h1) << ' ' << printhint(h2) << endl;
          }
          ptr++;
        }
    cout << "c [ipbip_hints] Total clauses: " << num_clauses << endl;
    cout << "c [ipbip_hints] Post-trim clauses: " << ptr << endl;
    report(1, "c [ipbip_hints] Elapsed time for output = %.2f seconds\n", tod() - output_start);
  }

  void output(const string &filename = "")
  {
    double output_start = tod();
    if (filename.empty())
    {
      for (auto x : clauses.clauses)
      {
        cout << x.clause_type << ' ';
        cout << x.c.output_clause();
        cout << " ; ";
        if (x.hints[0] == -2)
        {
          int id = x.hints[1];
          int t = clauses.current_new_format_items[id].size();
          for (int i = 0; i < t; i++)
          {
            auto &[cid, var, neg] = clauses.current_new_format_items[id][i];
            if (i + 1 == t)
              cout << '[' << printhint(cid) << ']' << endl;
            else
              cout << '[' << printhint(cid) << ' ' << vm.get_string(var, neg) << "] ";
          }
        }
        else
        {
          cout << printhint(x.hints[0]) << ' ' << printhint(x.hints[1]) << endl;
        }
      }
    }
    else
    {
      ofstream file(filename);
      if (file.is_open())
      {
        for (auto x : clauses.clauses)
        {
          file << x.clause_type << ' ';
          file << x.c.output_clause();
          file << " ; ";
          if (x.hints[0] == -2)
          {
            int id = x.hints[1];
            int t = clauses.current_new_format_items[id].size();
            for (int i = 0; i < t; i++)
            {
              auto &[cid, var, neg] = clauses.current_new_format_items[id][i];
              if (i + 1 == t)
                file << '[' << printhint(cid) << ']' << endl;
              else
                file << '[' << printhint(cid) << ' ' << vm.get_string(var, neg) << "] ";
            }
          }
          else
          {
            file << printhint(x.hints[0]) << ' ' << printhint(x.hints[1]) << endl;
          }
        }
      }
    }
    report(1, "c [ipbip_hints] Elapsed time for output = %.2f seconds\n", tod() - output_start);
  }

  /* void output(const string& filename = "") { */
  /*   if (filename.empty()) { */
  /*     for (auto x: clauses.clauses) { */
  /* 	cout << x.clause_type << ' '; */
  /* 	cout << x.c.output_clause(); */
  /* 	cout << " ; "; */
  /* 	cout << printhint(x.hints[0]) << ' ' << printhint(x.hints[1]) << endl; */
  /*     } */
  /*   } else { */
  /*     ofstream file(filename); */
  /*     if (file.is_open()) { */
  /* 	for (auto x: clauses.clauses) { */
  /* 	  file << x.clause_type << ' '; */
  /* 	  file << x.c.output_clause(); */
  /* 	  file << " ; "; */
  /* 	  file << printhint(x.hints[0]) << ' ' << printhint(x.hints[1]) << endl; */
  /* 	} */
  /* 	file.close(); */
  /*     } */
  /*   } */
  /* } */
};
