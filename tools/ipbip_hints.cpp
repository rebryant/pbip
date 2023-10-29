//#include <bits/stdc++.h>

//#include "ClauseManager.h"
//#include "PBConstraint.h"


#include <ctype.h>
#include "Manager.h"
#define endl '\n'
#define NEW_FORMAT true

vector<int> objective;
int nvars;

Manager mngr;

// ClauseManager mngr = ClauseManager();

bool digits_only(string st) {
  for (char& c : st) {
    if (!isdigit(c)) {
      return false;
    }
  }
  return true;
}


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


// PBConstraint str_to_constraint(string line) {
//   vector<tuple<string, int> > term_list;
//   vector<string> toks = split(line, " ");
//   for (int i = 0; i < toks.size(); i += 2) {
//     vector<string> constraints{ ">=", "<=", ">", "<", "=" };
//     if (std::find(constraints.begin(), constraints.end(), toks[i]) != constraints.end()) {
//       string constraint_type = toks[i];
//       int rhs_constant = stoi(toks[i + 1]);
//       return PBConstraint(term_list, rhs_constant, constraint_type);
//     }

//     string str_ci = toks[i];
//     string vi = toks[i + 1];

//     int ci = stoi(str_ci);

//     if (isVar(vi) || isVarNeg(vi)) {
//       term_list.push_back(make_tuple(vi, ci));
//     } else {
//       cerr << "Expected variable, received " << vi << endl;
//       exit(EXIT_FAILURE);
//     }
//   }

//   assert(false); // shouldn't be able to get here!
// }


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
  cout << "c Loading PB formula from " << formula_file << endl;
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
      //     cout << "ADDING INPUT " << clause(i).output_clause() << endl;
      mngr.add_input(i);

      //      cout << "c [loadFormula] Loaded constraint " << clause(i).output_clause() << endl;
    }
  }

  //  cout << "c Done loading PB formula (" << clause_idx << " clauses) from " << formula_file << endl;
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

void parseProof(string proof_file) {
  //  cout << "c Loading VeriPB proof from " << proof_file << endl;

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
  while (getline(in_file, line)) {
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
	//	cout << "c ipbip_hints: Loading " << line << endl;
        continue;
      } else if (command == "o") {
	//	cout << "c ipbip_hints: Loading " << line << endl;
	//        id += 1;
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

	//	cout << "c [parseProof] o constraint: loading " << clause(c).output_clause() << endl;
        mngr.add_input(c);
      } else if (command == "u") {
	//	cout << "c ipbip_hints: [" << u_count << "/" << rup_count << "] Loading " << line << endl;
	//        id += 1;

	//        PBConstraint c = str_to_constraint(line.substr(2, line.length() - 2));
	input_clause c = str_to_input_clause(line.substr(2, line.length() - 2));


	//	cout << "RUP CLAUSE: " << clause(c).output_clause() << endl;

	mngr.add_derive(c, NEW_FORMAT);
	u_count++;
        // mngr.derive(c, id);
      } else if (command == "w") {
        continue;
      } else if (command == "p") {
	//	cout << "c ipbip_hints: Loading " << line << endl;
	//        id += 1;

	rpn_input r = str_to_rpn_input(line.substr(2, line.length() - 2));
	mngr.add_rpn(r);
      } else if (command == "c") {
	//	cout << "c ipbip_hints: Loading " << line << endl;
        break;
      }
    }
  }

  // guard >= 1 assertion depending on whether it's already been seen
  input_clause final_unsat = str_to_input_clause(">= 1");
  mngr.add_derive(final_unsat, NEW_FORMAT);
  u_count++;

  //  cout << "c Done hinting VeriPB proof from " << proof_file << endl;
  return;
}


void emit_usage_msg_ERR () {
  cerr << "USAGE: ./ipbip_hints -f [.opb input file] -p [.pbp/veripb input file] -i [.ipbip output file]" << endl;
}

/*
 * USAGE: ./ipbip_hints -f [.opb input file] -p [.pbp/veripb input file] -i [.ipbip output file]
 * - .opb is the initial formula
 * - .pbp/.veripb is the solver-generated proof (in the VeriPB proof format)
 * - .ipbip is the output format (intermediate step for PBIP translation)
 */
int main(int argc, char** argv) {
  ios_base::sync_with_stdio(false);
  cin.tie(0);
  cout.tie(0);
  
  int opt;
  bool recFormula = false;
  bool recProof = false;
  bool recOutput = false;

  //  bool doLog = false;
    
  string formula_file;
  string proof_file;
  string ipbip_file;
  //  string log_file;

  cout << "c [ipbip_hints] Processing VeriPB file " << proof_file << endl;

  // Shut GetOpt error messages down (return '?'): 
  opterr = 0;

  // Retrieve the options:
  while ( (opt = getopt(argc, argv, "f:p:i:")) != -1 ) {  // for each option...
    switch ( opt ) {
    case 'f':
      recFormula = true;
      formula_file = optarg;
      break;
    case 'p':
      recProof = true;
      proof_file = optarg;
      break;
    case 'i':
      recOutput = true;
      ipbip_file = optarg;
      break;
    // case 'l':
    //   doLog = true;
    //   log_file = optarg;
    case '?':
      cerr << "Ill-formatted option: " << char(optopt) << endl;
      break;
    }
  }

  if (!recFormula) {
    cerr << "Missing input formula! [.opb input file]" << endl;
    emit_usage_msg_ERR();
    exit(EXIT_FAILURE);
  } else {
    //    cout << "c [Setup]: formula location " << formula_file << endl;
  }

  if (!recProof) {
    cerr << "Missing VeriPB proof! [.pbp/.veripb input file]" << endl;
    emit_usage_msg_ERR();
    exit(EXIT_FAILURE);
  } else {
    //    cout << "c [Setup]: proof location " << proof_file << endl;
  }

  if (!recOutput) {
    cerr << "Missing output destination! [.ipbip output file]" << endl;
    emit_usage_msg_ERR();
    exit(EXIT_FAILURE);
  } else {
    //    cout << "c [Setup]: .ipbip destination " << ipbip_file << endl;
  }

  // if (doLog) {
  //   cout << "c [Setup]: log location " << log_file << endl;
  // }

  //  cout << "c ----- [FORMULA] -----" << endl;
  loadFormula(formula_file);

  //  cout << "c ----- [VERIPB] -----" << endl;
  parseProof(proof_file);

  //  cout << "c ----- [IPBIP OUTPUT] -----" << endl;
  cout << "c [ipbip_hints] Emitting IPBIP proof to " << ipbip_file << endl;

  // if (doLog) {
  //   mngr.log_output(log_file);
  // }
  mngr.output(ipbip_file);
  //  cout << "c Done emitting IPBIP proof to " << ipbip_file << endl;

  return 0;
}
