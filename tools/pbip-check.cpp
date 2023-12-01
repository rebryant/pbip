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

#include <iostream>
#include <stdlib.h>
#include <unistd.h>
#include "signal.h"
#include <sys/time.h>
#include <string.h>

#include "report.h"
#include "tbdd.h"
#include "prover.h"
#include "pseudoboolean.hh"
#include "cnf2tbdd.hh"

using namespace trustbdd;

void usage(char *name) {
    printf("Usage: %s: [-h] [-b] [-S] [-v VERB] [-S] -i FILE.CNF -p FILE.pbip [-o FILE.lrat]\n", name);
    printf("  -h           Print this message\n");
    printf("  -v VERB      Set verbosity level\n");
    printf("  -b           Use BDDs for every step\n");
    printf("  -S           Disable SDP processing of CNF\n");
    printf("  -i FILE.cnf  Input CNF file\n");
    printf("  -p FILE.pbip PBIP Proof file\n");
    printf("  -o FILE.lrat Output proof file\n");
}

// Weird TBDD operations required to support unit propagation

// Set up unit propagation in RUP step
// Have lit == 0 for final conflict
static int tbdd_unit_propagate(tbdd tp, ilist context, int lit) {
    report(4, "Propagating unit %d using TBDD N%d\n", lit, tbdd_nameid(tp));
    ilist args = ilist_copy(context);
    for (int i = 0; i < ilist_length(args); i++)
	args[i] = -args[i];
    if (lit != 0)
	args = ilist_push(args, lit);
    bdd r = bdd_build_clause(args);
    tbdd t = tbdd_validate(r, tp);
    bdd node = r;
    ilist hlist = ilist_new(0);
    if (t.get_clause_id() != TAUTOLOGY)
	hlist = ilist_push(hlist, t.get_clause_id());
    while (node != bdd_false()) {
	bool positive = bdd_high(node) == bdd_true();
	int nid = node.dclause(positive ? DEF_LD : DEF_HD);
	hlist = ilist_push(hlist, nid);
	node = positive ? bdd_low(node) : bdd_high(node);
    }
    if (lit == 0)
	print_proof_comment(2, "Justify RUP conflict using TBDD N%d", tbdd_nameid(tp));
    else
	print_proof_comment(2, "Justify unit propagation of literal %d using TBDD N%d", lit, tbdd_nameid(tp));
    int prop_id = generate_clause(args, hlist);
    ilist_free(args);
    ilist_free(hlist);
    return prop_id;
}

// Set up unit propagation in RUP step
// Have lit == 0 for final conflict
static int target_unit_propagate(bdd rt, ilist context, int lit) {
    report(4, "Propagating unit %d using target N%d\n", lit, rt.nameid());
    ilist args = ilist_copy(context);
    if (lit != 0)
	args = ilist_push(args, -lit);
    bdd r = bdd_build_cube(args);
    for (int i = 0; i < ilist_length(args); i++)
	args[i] = -args[i];
    args = ilist_push(args, rt.xvar());
    int imp_id = bdd_prove_implication(r, rt);
    ilist hlist = ilist_new(0);
    if (imp_id != TAUTOLOGY)
	hlist = ilist_push(hlist, imp_id);
    bdd node = r;
    while (node != bdd_true()) {
	bool positive = bdd_low(node) == bdd_false();
	int nid = node.dclause(positive ? DEF_HU : DEF_LU);
	hlist = ilist_push(hlist, nid);
	node = positive ? bdd_high(node) : bdd_low(node);
    }
    if (lit == 0)
	print_proof_comment(2, "Justify RUP conflict with RUP target");
    else
	print_proof_comment(2, "Justify unit propagation of literal %d with RUP target", lit);
    int prop_id = generate_clause(args, hlist);
    ilist_free(args);
    ilist_free(hlist);
    return prop_id;
}


class pbip_line {
private:
    int line_id;
    int clause_id;
    ilist clause_literals;
    pb_constraint *constraint;

public:
    pbip_line(int id, pb_constraint *con) {
	line_id = id;
	tbdd trep = tbdd_null();
	clause_id = 0;
	clause_literals = NULL;
	constraint = con;
    }

    void validate_tbdd(tbdd t) {
	constraint->validate(t);
    }

    void validate_tbdd_with_and(tbdd t1, tbdd t2) {
	constraint->validate_with_and(t1, t2);
    }

    void add_clause(int id, ilist literals) {
	clause_id = id;
	clause_literals = ilist_copy(literals);
    }

    tbdd get_tbdd_validation() {
	if (constraint->is_validated())
	    return constraint->get_validation();
	if (clause_id > 0) {
	    tbdd t = tbdd_from_clause_with_id(clause_literals, clause_id);
	    constraint->add_validation(t);
	    return t;
	}
	err(true, "Have no way to validate PBIP line %d\n", line_id);
	return tbdd_null();
    }

    pb_constraint* get_constraint() { return constraint; }

    int get_id() { return line_id; }
    int get_clause_id() { return clause_id; }

};


// Parsing
int line_count = 0;

typedef enum { PARSE_EOL, PARSE_EOF, PARSE_OK, PARSE_ERR } parse_t;


static int skip_line(FILE *infile) {
  int c;
  while ((c = getc(infile)) != EOF) {
      if (c == '\n') {
	  line_count ++;
	  return c;
      }
  }
  return c;
}

static int next_cmd(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '*')
	    c = skip_line(infile);
	if (isspace(c)) {
	    if (c == '\n')
		line_count++;
	    continue;
	} else
	    break;
    }
    return c;
}

static parse_t find_character(FILE *infile, char fc) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    return PARSE_EOL;
	if (isspace(c))
	    continue;
	if (c == fc)
	    return PARSE_OK;
	ungetc(c, infile);
	return PARSE_ERR;
    }
    return PARSE_EOF;
}

static parse_t skip_to_nonspace(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    return PARSE_EOL;
	if (isspace(c))
	    continue;
	ungetc(c, infile);
	return PARSE_OK;
    }
    return PARSE_EOF;
}

static parse_t find_int(FILE *infile, int *valp) {
    parse_t p = skip_to_nonspace(infile);
    if (p == PARSE_OK) {
	if (fscanf(infile, "%d", valp) != 1)
	    p = PARSE_ERR;
    }
    return p;
}

static parse_t find_literal(FILE *infile, int *litp) {
    int wt = 1;
    int lit;
    if (find_character(infile, '~') == PARSE_OK)
	wt = -1;
    // Optional 'x'
    find_character(infile, 'x');
    if (find_int(infile, &lit) != PARSE_OK)
	return PARSE_ERR;
    *litp = lit * wt;
    return PARSE_OK;
}

class pbip_proof {
private:
    std::vector<pbip_line*> lines;
    FILE *pbip_file;
    std::unordered_set<int> *data_variables;
    cnf_tbdd *ct;
    bool only_bdd;
    bool use_sdp;
    int last_clause_count;

public:
    int added_clauses() {
	int lcc = last_clause_count;
	last_clause_count = total_clause_count;
	return last_clause_count - lcc;
    }

    pbip_proof(CNF *cnf, FILE *pbip, FILE *lrat, ilist variable_ordering, bool bdd, bool sdp)  {
	pbip_file = pbip;
	only_bdd = bdd;
	use_sdp = sdp;

	int clause_count = cnf->clause_count();
	ilist *clauses = new ilist[clause_count];
	for (int i = 0; i < clause_count; i++) {
	    Clause *cp = (*cnf)[i];
	    clauses[i] = cp->data();
	}
	int rcode;
	if ((rcode = tbdd_init_lrat(lrat, cnf->max_variable(), clause_count, clauses, variable_ordering)) != 0)
	    err(true, "Initialization failed.  Return code = %d\n", rcode);
	data_variables = new std::unordered_set<int>;
	// Run through proof file to identify data variables
	run(true);

	report(3, "c Data variables:");
	for (int v : *data_variables)
	    report(3, " %d", v);
	report(3, "\n");

	line_count = 0;
	last_clause_count = total_clause_count;
	rewind(pbip_file);
	ct = new cnf_tbdd(data_variables, use_sdp);
    }

    void run(bool data_only) {
	int lit;
	int cmd;
	while ((cmd = next_cmd(pbip_file)) != EOF) {
	    pb_constraint *pb = new pb_constraint(pbip_file);
	    if (pb->get_relation() == PB_NONE) {
		err(true, "Couldn't parse constraint on line %d\n", line_count+1);
	    }
	    if (!find_character(pbip_file, ';')) {
		err(true, "Line %d.  Missing semicolon\n", line_count+1);
	    }
	    if (data_only) {
		skip_line(pbip_file);
		ilist literals = pb->get_literals();
		for (int idx = 0; idx < ilist_length(literals); idx++) {
		    int lit = literals[idx];
		    if (lit < 0)
			lit = -lit;
		    data_variables->insert(lit);
		}
	    } else {
		pbip_line *line = new pbip_line(lines.size() + 1, pb);
		if (verblevel >= 4) {
		    report(3, "c Read PBIP line: ");
		    pb->show(stdout);
		    report(3, "\n");
		}
		lines.push_back(line);
		switch (cmd) {
		case 'i':
		    do_input(line);
		    break;
		case 'u':
		    do_rup(line);
		    break;
		case 'a':
		    do_assertion(line);
		    break;
		default:
		    err(true, "Line %d.  Invalid command '%c'\n", line_count+1, cmd);
		    break;
		}
	    }
	}
	if (!data_only) {
	    report(1, "c Reached end of PBIP file.  %d lines.  Processed %d commands\n", line_count, (int) lines.size());
	    tbdd_done();
	}
    }

private:
    void do_input(pbip_line *line) {
	ilist clause_list = ilist_new(0);
	int id;
	while (find_int(pbip_file, &id)) {
	    clause_list = ilist_push(clause_list, id);
	}
	if (only_bdd || ilist_length(clause_list) > 1) {
	    tbdd t = ct->extract_tbdd(clause_list);
	    line->validate_tbdd(t);
	} else {
	    int id = clause_list[0];
	    line->add_clause(id, get_input_clause(id));
	}
	ilist_free(clause_list);
	report(2, "c Processed Input %d.  %d added clauses\n", line->get_id(), added_clauses());
    }

    void do_rup(pbip_line *line) {
	ilist unit_literals = ilist_new(0);
	ilist rup_hint = ilist_new(0);
	ilist try_clause = only_bdd ? NULL : line->get_constraint()->try_clause();
	bool bdd_target = try_clause == NULL;
	ilist target_clause;
	bdd rtarget = bdd_false();
	if (bdd_target) {
	    rtarget = line->get_constraint()->generate_bdd();
	    target_clause = ilist_new(0);
	    if (rtarget != bdd_false())
		target_clause = ilist_push(target_clause, rtarget.xvar());
	} else {
	    target_clause = ilist_copy(try_clause);
	}
	bool conflict_generated = false;
	while (true) {
	    bool done = false;
	    int id = 0;
	    int lit = 0;
	    switch (find_character(pbip_file, '[')) {
	    case PARSE_EOF:
	    case PARSE_EOL:
		done = true;
		break;
	    case PARSE_ERR:
		err(true, "Line %d.  Expecting '[' in RUP hint\n", line_count+1);
		break;
	    case PARSE_OK:
		break;
	    }
	    if (done) {
		if (!conflict_generated) {
		    err(true, "Line %d.  Complete RUP hints without final conflict\n", line_count+1);
		}
		break;
	    }
	    if (find_int(pbip_file, &id) != PARSE_OK) 
		err(true, "Line %d.  Expecting integer ID in RUP hint\n", line_count+1);
	    if (id < 0)
		id = -id;
	    if (id == 0 || id > line->get_id())
		err(true, "Line %d.  Invalid clause ID %d in RUP hint\n", line_count+1, id);
	    if (find_literal(pbip_file, &lit) != PARSE_OK)
		lit = 0;
	    if (find_character(pbip_file, ']') != PARSE_OK)
		err(true, "Line %d.  Expecting ']' in RUP hint\n", line_count+1);
	    int prop_id = 0;
	    if (id == line->get_id()) {
		if (bdd_target)
		    prop_id = target_unit_propagate(rtarget, unit_literals, lit);
		else
		    prop_id = TAUTOLOGY;
	    } else {
		pbip_line *pline = lines[id-1];
		if (!only_bdd)
		    prop_id = pline->get_clause_id();
		if (prop_id == 0)
		    prop_id = tbdd_unit_propagate(pline->get_tbdd_validation(), unit_literals, lit);
	    }
	    if (prop_id != TAUTOLOGY)
		rup_hint = ilist_push(rup_hint, prop_id);
	    if (lit == 0)
		conflict_generated = true;
	    else
		unit_literals = ilist_push(unit_literals, lit);
	    
	}
	if (bdd_target)
	    print_proof_comment(2, "RUP step #%d.  Validation of target N%d", line->get_id(), rtarget.nameid());
	else
	    print_proof_comment(2, "RUP step #%d.  Validation of target clause", line->get_id());
	int vid = generate_clause(target_clause, rup_hint);
	if (bdd_target) {
	    tbdd target(rtarget, vid);
	    pb_constraint *gen_con = line->get_constraint();
	    gen_con->add_validation(target);
	    if (try_clause != NULL) {
		if (verblevel >= 4) {
		    printf("Creating clausal representation of RUP target: [");
		    ilist_print(try_clause, stdout, " ");
		    printf("]\n");
		}
		int cid = gen_con->validate_clause(try_clause);
		line->add_clause(cid, try_clause);
	    }
	} else {
	    line->add_clause(vid, target_clause);
	}

	ilist_free(unit_literals);
	ilist_free(rup_hint);
	ilist_free(target_clause);
	report(2, "c Processed RUP %d.  %d added clauses\n", line->get_id(), added_clauses());
    }

    void do_assertion(pbip_line *line) {
	ilist hint_ids = ilist_new(0);
	int id;
	report(4, "   Hints:");
	while (find_int(pbip_file, &id)) {
	    hint_ids = ilist_push(hint_ids, id);
	    report(4, " %d", id);
	}
	report(4, "\n");
	if (ilist_length(hint_ids) < 1)
	    err(true, "Line %d.  Expecting hint(s)\n", line_count+1);
	if (ilist_length(hint_ids) > 2)
	    err(true, "Line %d.  Too many hints\n", line_count+1);

	int h1 = hint_ids[0];
	if (h1 < 1 || h1 >= line->get_id())
	    err(true, "Line %d.  Invalid hint id %d\n", line_count+1, h1);
	pbip_line *line1 = lines[h1-1];
	tbdd t1 = line1->get_tbdd_validation();
	if (ilist_length(hint_ids) == 1)
	    line->validate_tbdd(t1);
	else {
	    int h2 = hint_ids[1];
	    if (h2 < 1 || h2 >= line->get_id())
		err(true, "Line %d.  Invalid hint id %d\n", line_count+1, h2);
	    pbip_line *line2 = lines[h2-1];
	    tbdd t2 = line2->get_tbdd_validation();
	    line->validate_tbdd_with_and(t1, t2);
	}
	pb_constraint *gen_con = line->get_constraint();
	ilist gen_clause = only_bdd ? NULL : gen_con->try_clause();
	if (gen_clause != NULL) {
	    if (verblevel >= 4) {
		printf("Creating clausal representation of assertion: [");
		ilist_print(gen_clause, stdout, " ");
		printf("]\n");
	    }
	    int cid = gen_con->validate_clause(gen_clause);
	    line->add_clause(cid, gen_clause);
	}
	ilist_free(hint_ids);
	report(2, "c Processed Assertion %d.  %d added clauses\n", line->get_id(), added_clauses());
    }
};

int main(int argc, char *argv[]) {
    FILE *cnf_file = NULL;
    FILE *pbip_file = NULL;
    FILE *lrat_file = NULL;
    ilist variable_ordering = NULL;
    bool only_bdd = false;
    bool use_sdp = true;
    int vlevel = 1;
    int c;
    while ((c = getopt(argc, argv, "hbSv:i:p:o:")) != -1) {
	switch (c) {
	case 'h':
	    usage(argv[0]);
	    return 0;
	case 'b':
	    only_bdd = true;
	    break;
	case 'S':
	    use_sdp = false;
	    break;
	case 'v':
	    vlevel = atoi(optarg);
	    break;
	case 'i':
	    cnf_file = fopen(optarg, "r");
	    if (cnf_file == NULL)
		err(true, "Couldn't open file %s\n", optarg);
	    break;
	case 'p':
	    pbip_file = fopen(optarg, "r");
	    if (pbip_file == NULL)
		err(true, "Couldn't open file %s\n", optarg);
	    break;
	case 'o':
	    lrat_file = fopen(optarg, "w");
	    if (lrat_file == NULL) 
		err(true, "Couldn't open file %s\n", optarg);
	    break;
	}
    }
    set_verblevel(vlevel);
    tbdd_set_verbose(vlevel);

    if (!cnf_file) {
	report(0, "Require CNF file\n");
	usage(argv[0]);
	exit(1);
    }
    if (!pbip_file) {
	report(0, "Require PBIP file\n");
	usage(argv[0]);
	exit(1);
    }
    if (!lrat_file) {
	report(0, "Require CNF file\n");
	usage(argv[0]);
	exit(1);
    }
    CNF *cnf = new CNF(cnf_file);
    if (cnf->failed())
	err(true, "Exiting\n");
    else
	report(1, "c Read CNF file with %d variables and %d clauses\n", cnf->max_variable(), cnf->clause_count());

    report(1, "PBIP to LRAT conversion options:\n");
    report(1, "  BDD Only: %s\n", only_bdd ? "true" : "false");
    report(1, "  Symbolic DP: %s\n", use_sdp ? "true" : "false");

    variable_ordering = ilist_new(cnf->max_variable());
    ilist_resize(variable_ordering, cnf->max_variable());
    for (int i = 0; i < cnf->max_variable(); i++)
	variable_ordering[i] = i+1;


    double start = tod();
    pbip_proof p(cnf, pbip_file, lrat_file, variable_ordering, only_bdd, use_sdp);
    p.run(false);
    report(1, "\nc Elapsed time for proof generation = %.2f seconds\n", tod() - start);
    return 0;
}
