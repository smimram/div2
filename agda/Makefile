all:
	agda Sub1.agda
	agda Div2.agda
	agda Spaces.agda

clean:
	rm -f *.agdai

html:
	mkdir -p html
	agda --html Div2.agda
	cd html && ln -s Div2.html index.html
