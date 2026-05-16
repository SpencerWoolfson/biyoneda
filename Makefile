TEX_DIR = paper
TEX     = Biyoneda

.PHONY: all clean

all: $(TEX).pdf

$(TEX).pdf: $(TEX_DIR)/$(TEX).tex
	cd $(TEX_DIR) && latexmk -pdf -f -interaction=nonstopmode $(TEX).tex || test -f $(TEX).pdf
	cp $(TEX_DIR)/$(TEX).pdf $@

clean:
	cd $(TEX_DIR) && latexmk -C
	rm -f $(TEX_DIR)/$(TEX).bbl $(TEX_DIR)/$(TEX).run.xml
	rm -f $(TEX).pdf
