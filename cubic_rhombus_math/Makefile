# make pdf DIR=preprints/<directory>   builds one manuscript
# make overview                        builds overview.pdf
# make ledger                          verifies the hash chain
pdf:
	cd $(DIR) && pdflatex -interaction=nonstopmode manuscript.tex && pdflatex -interaction=nonstopmode manuscript.tex

overview:
	pdflatex -interaction=nonstopmode overview.tex && pdflatex -interaction=nonstopmode overview.tex

ledger:
	python3 tools/industrial_mathematics.py ledger-check --out .

verify:
	cd tools && python3 verify.py
