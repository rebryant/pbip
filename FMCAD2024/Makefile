NAME = FMCAD2024
LATEX = pdflatex # xelatex
BIBTEX = bibtex

chapters:
	$(LATEX) -shell-escape $(NAME).tex
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME).tex
	$(LATEX) $(NAME).tex

clean:
	rm -f *.blg *.bbl *.aux *.log *.dvi *.out *.idx *.log *.lof *.lot
