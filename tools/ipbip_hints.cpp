/*========================================================================
  Copyright (c) 2023 Randal E. Bryant, Marijn J. H. Heule,
  Karthik Nukala, Soumyaditya Choudhuri, Carnegie Mellon University
  
  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
========================================================================*/

#include <ctype.h>
#include "Manager.h"
#include "report.h"

#define endl '\n'

// Switches between parsing VeriPB 1.0 and VeriPB 2.0 proof formats
// TODO: full support for 2.0
#define VERIPB_VERSION 1

vector<int> objective;
int nvars;

Manager mngr;

void usage(char *name) {
  printf("Usage: %s [-h] [-v VERB] [-f] FILE.opb [-p] FILE.veripb [-i] FILE.ipbip" , name);
  printf("  -h              Print this message\n");
  printf("  -v VERB         Set verbosity level\n");
  printf("  -f FILE.opb     Input OPB file\n");
  printf("  -p FILE.veripb  Input VeriPB file\n");
  printf("  -i FILE.ipbip   IPBIP Proof file\n");
}


// Utilities for processing/parsing constraints ----------

// (0-9)+
bool digits_only(string st) {
  if (st.length() == 0) {
    return false;
  }
  for (char& c : st) {
    if (!isdigit(c)) {
      return false;
    }
  }
  return true;
}

// Variables must be of the form (a-zA-Z)+(0-9)+
bool isVar(string tok) {
  bool flag = false;
  for (int i = 0; i < tok.length(); i++) {
    if (flag) {
      auto sb = tok.substr(i);
      if (sb.length() == 0) {
        return true;
      }
      return digits_only(sb);
    }

    if (isalpha(tok.at(i))) {
      continue;
    } else {
      flag = true;
    }
  }

  return true;
}

bool isVarNeg(string tok) {
  if (tok.at(0) == '~') {
    return isVar(tok.substr(1));
  } else {
    return false;
  }
}

vector<string> split(string s, string delimiter) {
  size_t pos_start = 0, pos_end, delim_len = delimiter.length();
  string token;
  vector<string> res;

  while ((pos_end = s.find(delimiter, pos_start)) != string::npos) {
    token = s.substr (pos_start, pos_end - pos_start);
    pos_start = pos_end + delim_len;
    res.push_back (token);
  }

  res.push_back (s.substr (pos_start));
  return res;
}


input_clause str_to_input_clause(string line) {
  list<term> l;

  vector<string> toks = split(line, " ");
  
  for (int i = 0; i < toks.size() ; i += 2) {
    vector<string> constraints{ ">=", "<=", ">", "<", "=" };
    auto c_beg = constraints.begin(); auto c_end = constraints.end();

    // Case: found constraint { ">=", "<=", ">", "<", "=" }
    if (find(c_beg, c_end, toks[i]) != c_end) { 
      if (toks[i] != ">=") {
	assert(false); // don't support not >= constraints!
      }

      int rhs = stoi(toks[i + 1]);

      input_clause input = input_clause(l, rhs);

      return input;
    }

    // Case: working with ci vi pairs
    string str_ci = toks[i];
    int ci = stoi(str_ci);

    term t = vm.get_term_with_coeff(toks[i + 1], ci);
    l.push_back(t);

  }

  assert(false); // lines need to end with constraint/rhs!
}


bool isnum(string s) {
  for (auto c : s) {
    if (!isdigit(c)) {
      return false;
    }
  }
  return true;
}


rpn_input str_to_rpn_input(string line) {
  list<rpn_token> l;

  vector<string> toks = split(line, " ");
  for (string tok : toks) {
    if (isnum(tok)) {
      l.push_back(rpn_token(stoi(tok)));
    } else {
      l.push_back(rpn_token(tok[0]));
    }
  }

  return rpn_input(l);
}

void loadFormula(string formula_file) {
  // cout << "c Loading PB formula from " << formula_file << endl;
  ifstream in_file (formula_file);
  if (in_file.fail()) {
    //    cout << "Formula file " << formula_file << " doesn't exist!" << endl;
    exit(EXIT_FAILURE);
  } 
  string line;

  int clause_idx = 0;
  while (getline(in_file, line)) {

    vector<string> toks = split(line, " ");

    if (toks[0] == "*") {
      nvars = stoi(toks[2]);
      mngr = Manager(nvars);
    } else if (toks[0] == "min:") {
      int tok_idx = 1;
      for (int i = 0; i < nvars + 1; i++) {
        objective.resize(nvars);
        if (toks[tok_idx] == "") {
          break;
        } else if (toks[tok_idx] == ";") {
          break;
        } else {
          objective[i] = stoi(toks[tok_idx]);
          tok_idx += 2;
        }
      }
    } else {
      clause_idx += 1;
      input_clause i = str_to_input_clause(line);
      mngr.add_input(i);
    }
  }
}


void emit_proof_msg_ERR (string command) {
  cerr << "Unsupported proof rule: " << command << endl;
}

int count_RUP(string proof_file) {
  ifstream in_file (proof_file);
  int count = 0;

  string line;
  while (getline(in_file, line)) {
    vector<string> toks = split(line, " ");
    if (toks[0] == "u") {
      count++;
    }
  }

  return count;
}

vector<string> proof_lines;

void loadProof(string proof_file) {
  //  cout << "[ipbip_hints] loadProof" << endl;
  ifstream in_file (proof_file);
  string line;
  while (getline(in_file, line)) {
    proof_lines.push_back(line);
  }
  return;
}

void find_strongest_opt() {
  //  cout << "[ipbip_hints] find_strongest_opt" << endl;
  for (int i = proof_lines.size() - 1; i >= 0; i--) {
    string line = proof_lines[i];
    vector<string> toks = split(line, " ");
    string command = toks[0];
    if (command == "o" || command == "soli") {
      vector<string> assn = vector<string>(toks.begin() + 1, toks.end());

      int found_size = 0;
      list<term> l;
      // vector<tuple<string, int> > term_list;
      for (auto& a : assn) {
	term t = vm.get_term(a);
	t.neg = false;
	  
	l.push_back(t);

	if (a[0] != '~') {
	  found_size += 1;
	}
      }

      int new_rhs = found_size + 1;
	
      input_clause c = input_clause(l, new_rhs);
      clause strongest_opt = clause(c);
      mngr.clauses.register_opt(strongest_opt);
      break;
    }
  }
  return;
  
}

void parseProof(string proof_file) {
  // cout << "c Loading VeriPB proof from " << proof_file << endl;

  int rup_count = count_RUP(proof_file);
  
  ifstream in_file (proof_file);
  if (in_file.fail()) {
    //    cout << "Proof file " << proof_file << " doesn't exist!" << endl;
  }

  int u_count = 1;

  int linenum = 1;

  string line;

  //  int id = 0; // CHANGE THIS
  //   int id = mngr.next_clause_id - 1;
  //  while (getline(in_file, line)) {
  for (int i = 0; i < proof_lines.size(); i++) {
    string line = proof_lines[i];
    // cout << "c ipbip_hints: Loading " << line << endl;
    if (linenum == 1) {
      
      linenum += 1;
      continue;
    } else {
      linenum += 1;
      vector<string> toks = split(line, " ");
      string command = toks[0];
      if (command == "#" || command == "*") {
        continue;
      } else if (command == "f") {
        continue;
      } else if (command == "o" || command == "soli") {
	mngr.clauses.add_opt();
	
      } else if (command == "u") {
	if (u_count % 100 == 0) {
    report(1, "c [ipbip_hints] elapsed: %d RUP steps, total: %d RUP steps\n", u_count, rup_count);
    // cout << "c ipbip_hints: [" << u_count << "/" << rup_count << "] Loading " << line << endl;
  }
	input_clause c = str_to_input_clause(line.substr(2, line.length() - 2));
	mngr.add_derive(c, nvars);
	u_count++;
        // mngr.derive(c, id);
      } else if (command == "w") {
        continue;
      } else if (command == "p") {
	rpn_input r = str_to_rpn_input(line.substr(2, line.length() - 2));
	mngr.add_rpn(r);
      } else if (command == "c") {
        break;
      }
    }
  }

  // guard >= 1 assertion depending on whether it's already been seen
  input_clause final_unsat = str_to_input_clause(">= 1");
  mngr.add_derive(final_unsat, nvars);
  u_count++;

  //  cout << "c Done hinting VeriPB proof from " << proof_file << endl;
  return;
}


void emit_usage_msg_ERR () {
  cerr << "USAGE: ./ipbip_hints -f [.opb input file] -p [.pbp/veripb input file] -i [.ipbip output file]" << endl;
}

bool uninit(string s) {
  return s == "";
}

int main(int argc, char *argv[]) {
  string opb_file;
  string veripb_file;
  string ipbip_file;

  int vlevel = 1;
  int c;
  while ((c = getopt(argc, argv, "hv:f:p:i:")) != -1) {
    switch (c) {
    case 'h':
      usage(argv[0]);
      return 0;

    case 'v':
      vlevel = atoi(optarg);
      break;

    case 'f':
      opb_file = optarg;
      report(2, "c [ipbip_hints] opb_file = %s\n", opb_file.c_str());
      if (opb_file == "")
	err(true, "Couldn't open .opb file %s\n", optarg);
      break;
    case 'p':
      veripb_file = optarg;
      report(2, "c [ipbip_hints] veripb_file = %s\n", veripb_file.c_str());
      if (veripb_file == "")
	err(true, "Couldn't open .veripb file %s\n", optarg);
      break;
    case 'i':
      ipbip_file = optarg;
      report(2, "c [ipbip_hints] ipbip_file = %s\n", ipbip_file.c_str());
      if (ipbip_file == "")
	err(true, "Couldn't open .ipbip file %s\n", optarg);
      break;
    }
  }

  set_verblevel(vlevel);

  if (uninit(opb_file)) {
      report(0, "Require OPB file\n");
      usage(argv[0]);
      exit(1);
  }
  
  if (uninit(veripb_file)) {
      report(0, "Require VeriPB file\n");
      usage(argv[0]);
      exit(1);
  }

  if (uninit(ipbip_file)) {
      report(0, "Require IPBIP file\n");
      usage(argv[0]);
      exit(1);
  }

  
    loadFormula(opb_file);
    loadProof(veripb_file);
    report(2, "c [ipbip_hints] Done loading formula + proof\n");
    find_strongest_opt();
    double start = tod();
    parseProof(veripb_file);
    report(2, "c [ipbip_hints] Done hinting proof\n");
    // mngr.output(ipbip_file);
    // auto basename = split(ipbip_file, ".")[0];
    // string ipbip_trimmed = basename + "-trimmed.ipbip";
    report(1, "\n\n");
    report(1, "c ipbip_hints statistics\n");
    report(1, "c -----------------------\n");
    mngr.trimoutput(ipbip_file);
    int max_clique_size = mngr.clauses.clauses[mngr.clauses.opt_id].c.rhs - 1;
    report(1, "c [ipbip_hints] Maximum clique size: %d\n", max_clique_size);
    report(1, "c [ipbip_hints] Elapsed time for proof hinting = %.2f seconds\n", tod() - start);
    report(2, "c [ipbip_hints] Done outputting .ipbip file\n");

    return 0;
}
