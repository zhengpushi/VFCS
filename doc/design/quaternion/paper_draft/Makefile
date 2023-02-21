
pdfs := $(patsubst %.tex,%.pdf,$(wildcard *.tex))

all : $(pdfs)

%.pdf : %.tex
	pdflatex --shell-escape $< -o $@

%.docx : %.tex
	pandoc -s $< -o $@

docx: *.docx

view: *.pdf
	open *.pdf

clean:
	-rm *.aux *.log *.spl *.upa *.upb *.out _region_.tex
	-rm _minted-* -r

cleanall: clean
	rm *.pdf

.PHONY: clean
