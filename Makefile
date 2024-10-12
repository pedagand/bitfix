all: paper.pdf

quick: paper.tex paper.bib
	pdflatex paper.tex

paper.pdf: paper.tex paper.bib
	pdflatex paper.tex
	bibtex paper
	pdflatex paper.tex
	pdflatex paper.tex

clean:
	rm paper.pdf
