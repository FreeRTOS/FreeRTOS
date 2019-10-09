# Documentation Generation

## Requirements

You'll need the following software:
- [Doxygen](http://www.doxygen.nl/index.html)
- [Sphinx](http://www.sphinx-doc.org/en/master/index.html)
- LaTeX (For building a PDF)

### Ubuntu

You can install the required software on Ubuntu with the following:

```
sudo apt install doxygen python3-sphinx python3-breathe graphviz python3-pydot
sudo apt install texlive-full latexmk
```

The second line can be omitted if you don't intend to build the PDF.

### MacOS

You can install the required software on MacOS with the following:

```
brew install doxygen sphinx-doc graphviz
brew cask install mactex
```

The second line can be omitted if you don't intend to build the PDF.

## Building the Docs

You can generate both the HTML and PDF documentation with
```
make
```

Or only the HTML or PDF docs using

```
make html
```
or

```
make pdf
```

You can clean the build files and outputs with

```
make clean
```

