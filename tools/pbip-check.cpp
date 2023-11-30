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
	clause_id = -1;
	clause_literals = NULL;
	constraint = con;
    }

    void validate_tbdd(tbdd t) {
	constraint->validate(t);
    }

    void validate_tbdd_with_and(tbdd t1, tbdd t2) {
	constraint->validate_with_and(t1, t2);
    }
    pb_constraint* get_constraint() { return constraint; }
    int get_id() { return line_id; }
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


public:
    pbip_proof(CNF *cnf, FILE *pbip, FILE *lrat, ilist variable_ordering, bool bdd, bool sdp)  {
	pbip_file = pbip;
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
		if (verblevel >= 3) {
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
	report(2, "c Processing Input %d\n", line->get_id());
	ilist clause_list = ilist_new(0);
	int id;
	while (find_int(pbip_file, &id)) {
	    clause_list = ilist_push(clause_list, id);
	}
	tbdd t = ct->extract_tbdd(clause_list);
	line->validate_tbdd(t);
	ilist_free(clause_list);
    }

    void do_rup(pbip_line *line) {
	report(2, "c Processing RUP %d\n", line->get_id());
	ilist id_list = ilist_new(0);
	ilist literal_list = ilist_new(0);
	report(3, "c Processing RUP command.  Hints: ");
	while (true) {
	    bool done = false;
	    int id;
	    int lit;
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
	    if (done)
		break;
	    if (find_int(pbip_file, &id) != PARSE_OK) 
		err(true, "Line %d.  Expecting integer ID in RUP hint\n", line_count+1);
	    if (id < 0)
		id = -id;
	    bool found_plit = find_literal(pbip_file, &lit) == PARSE_OK;
	    if (find_character(pbip_file, ']') != PARSE_OK)
		err(true, "Line %d.  Expecting ']' in RUP hint\n", line_count+1);
	    id_list = ilist_push(id_list, id);
	    if (found_plit) {
		report(3, " [%d %d]", id, lit);
		literal_list = ilist_push(literal_list, lit);
	    } else {
		report(3, " [%d]]", id);
	    }
	}
	report(3, "\n");
	ilist_free(id_list);
	ilist_free(literal_list);
    }

    void do_assertion(pbip_line *line) {
	report(2, "c Processing Assertion %d\n", line->get_id());
	ilist hint_ids = ilist_new(0);
	int id;
	report(3, "   Hints:");
	while (find_int(pbip_file, &id)) {
	    hint_ids = ilist_push(hint_ids, id);
	    report(3, " %d", id);
	}
	report(3, "\n");
	if (ilist_length(hint_ids) < 1)
	    err(true, "Line %d.  Expecting hint(s)\n", line_count+1);
	if (ilist_length(hint_ids) > 2)
	    err(true, "Line %d.  Too many hints\n", line_count+1);

	int h1 = hint_ids[0];
	if (h1 < 1 || h1 >= line->get_id())
	    err(true, "Line %d.  Invalid hint id %d\n", line_count+1, h1);
	pbip_line *line1 = lines[h1-1];
	pb_constraint *con1 = line1->get_constraint();
	tbdd t1 = con1->get_validation();
	if (ilist_length(hint_ids) == 1)
	    line->validate_tbdd(t1);
	else {
	    int h2 = hint_ids[1];
	    if (h2 < 1 || h2 >= line->get_id())
		err(true, "Line %d.  Invalid hint id %d\n", line_count+1, h2);
	    pbip_line *line2 = lines[h2-1];
	    pb_constraint *con2 = line2->get_constraint();
	    tbdd t2 = con2->get_validation();
	    line->validate_tbdd_with_and(t1, t2);
	}
	ilist_free(hint_ids);
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

    variable_ordering = ilist_new(cnf->max_variable());
    ilist_resize(variable_ordering, cnf->max_variable());
    for (int i = 0; i < cnf->max_variable(); i++)
	variable_ordering[i] = i+1;

    pbip_proof p(cnf, pbip_file, lrat_file, variable_ordering, only_bdd, use_sdp);
    p.run(false);
    return 0;
}
