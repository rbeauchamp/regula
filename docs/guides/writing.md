# Writing rules

Obey the writing rules of ASD-STE100 Simplified Technical English, Issue 9 (January 2025), when you write or change a Markdown document of this repository. ASD-STE100 is a document of the Aerospace, Security and Defence Industries Association of Europe (ASD). This repository contains no part of that document. To read ASD-STE100, get a copy from ASD.

ASD-STE100 is a registered trademark of ASD. This project uses the name only to identify that document. ASD did not examine this project and gave no approval to it.

These writing rules are for the documents of this repository. They are not a part of the Regula standard, and no writing rule is a requirement of that standard. The checker does not use them for a project that uses Regula. Each check of these writing rules is a check of the repository. It is the same type of check as the check of rule IDs in documents, and it has no rule ID.

The vocabulary of the project is [`CONTEXT.md`](../../CONTEXT.md). It gives the technical nouns and the technical verbs of the project. Rule 1.5 and rule 1.12 of ASD-STE100 let a project have such words.

## Writing rules with a check

The command `./scripts/verify.sh docs` does the checks of the tracked Markdown documents. Each check has a name.

| Check | Rule | The check does not accept |
| --- | --- | --- |
| C1 | 6.3 | A sentence of more than 25 words in a paragraph, in an item of an unordered list or in a table cell. |
| C2 | 5.1 | A sentence of more than 20 words in an item of an ordered list, or in a block that starts with `WARNING:` or `CAUTION:`. |
| C3 | 6.6 | A paragraph of more than six sentences. |
| C4 | 8.1 | A semicolon. |
| C5 | 4.2 | A contraction: a word that has `n't`, `'re`, `'ve`, `'ll`, `'d` or `'m` at its end, or one of 11 words, for example `it's`. |
| C6 | 1.8 and 1.11 | A name that `CONTEXT.md` gives as replaced. |
| C7 | A rule of the project | A word of the table "Replaced words" of `CONTEXT.md`. |
| C8 | A rule of the project | One of the abbreviations `e.g.`, `i.e.`, `etc.`, `vs.` and `cf.`. |
| C9 | The format | A `CONTEXT.md` that is not the text of a vocabulary, or a source path that is not a tracked file. |
| B1 | The baseline | A document with findings that the baseline does not give. |
| B2 | The baseline | A baseline that gives more findings than the baseline of the base revision. |

### How the checks read a document

The checks C1 to C8 do not read Markdown syntax. The md4c parser reads each document in the GitHub dialect, and the checks read the blocks that the parser gives. A block is a heading, a paragraph, a paragraph of a list item or a table cell. A code block has no text for the checks. The description of an image is text of its block.

The checks do not read code. Put each identifier, path, command and program output in code font.

### The vocabulary file

`CONTEXT.md` has a title, two or three lines after the title and a maximum of five tables. Each row of a table is one line. The function `write` of [`RegulaCore/Vocabulary.lean`](../../lean/RegulaCore/Vocabulary.lean) gives the text of a vocabulary. C9 accepts a file only if it is that text. Thus one vocabulary has only one text, and a diff shows one line for each changed row.

C9 also does not accept a file with one of these defects:

- A term that is not one, two or three words.
- A category of a noun that is not one of the 22 categories of rule 1.5.
- A category of a verb that is not one of the 16 categories of rule 1.12.
- A definition that is not one sentence of 25 words or less with a period at its end.
- Rows of a table that are not in the sequence of their terms.
- Two rows with the same term. The two rows can be in one table or in two tables, for example a noun row and a verb row.
- A name that two rows replace.
- A term that is also a replaced name or a replaced word.
- A replaced name that is also a replaced word.
- A cell with a `|` character.

The check compares terms, names and words in lowercase. The statement `Draft.WellFormed` gives each defect of this list. It also gives defects of the form of a cell, for example a version that is not a number.

C9 also does not accept a row with a source path that is not a tracked file of the repository.

A second project can use the `Shared` tables of this `CONTEXT.md`. The `CONTEXT.md` of that project has the line `Shared vocabulary:` with the name of the package, and it has no `Shared` table. The option `--shared` gives the `CONTEXT.md` of the package to the check. The check then reads the rows of that project together with the `Shared` tables of the package, but not with its other tables. Thus a `Project` row cannot have the term of a `Shared` row. The source path of a `Shared` row must be a tracked file of the repository of the package.

### Words and sentences

The checks C1 to C8 and the check of a definition use these definitions of a word and of a sentence. The definitions are in [`RegulaCore/ControlledText.lean`](../../lean/RegulaCore/ControlledText.lean).

- A word is a sequence of ASCII letters, digits, hyphens and apostrophes that has a letter or a digit (rule 8.7). No such character is immediately before the word or immediately after it.
- A code span is one word. Two code spans with no character between them are also one word.
- A character that is not ASCII is one word. But the check reads some of these characters as punctuation or as a space. They are two apostrophes, the quotation marks, two dashes, the ellipsis and the usual spaces.
- Text from a double quotation mark to the next double quotation mark is one word. The check does not read the words in it.
- Text from an opening parenthesis to a closing parenthesis, with no parenthesis between them, is one word of its sentence. The check also reads this text as one or more sentences (rule 8.5).
- A sentence can stop after a period, a question mark or an exclamation mark. It stops there if a space and the start of a new sentence are immediately after that mark.
- A new sentence starts with an uppercase letter, a digit, a code span, quoted text or a parenthesis.
- A sentence also stops at the end of its block. Thus the text before a list and each list item are different sentences (rule 8.4).
- A heading has no sentence for C1 to C3.

These definitions give these results:

- The number `4.34.1` is three words, if it is not in code font.
- Each word of a title or of a proper noun is one word.
- If parentheses contain parentheses, only the text in the parentheses that contain no parenthesis is one word. The other words are words of the sentence.

To let the checks find each sentence, start a sentence with an uppercase letter or with a code span. Do not write an abbreviation that has a period at its end.

### The count of the check and the count of ASD-STE100

Rules 8.4 to 8.7 of ASD-STE100 tell how to count the words of a sentence. The count of the check for a sentence is not smaller than the count of those rules, if the text obeys these three conditions:

- Condition 1: Each item that those rules count as one word has a letter or a digit. A character that is not a letter, a digit, a hyphen or an apostrophe is between two such items.
- Condition 2: Each double quotation mark is one of two marks that have quoted text between them.
- Condition 3: Each end of a sentence that the check finds is the end of a sentence for a reader. Thus no abbreviation with a period is before a space and an uppercase letter.

Lean does not prove these conditions, because they are about the meaning of the text. A reviewer examines them. If a text does not obey condition 3, the count of the check can be too small.

The check does not accept some sentences that are in the limit of rules 8.4 to 8.7. For example, the check gives two or more words to a decimal number that is not in code font. The check also gives one word to each word of a title or of a proper noun.

Lean proves these facts about the definitions:

- Each definition gives only one result for a text, and the function of the check gives that result (the theorems `runs_iff`, `folded_iff` and `divided_iff`).
- Before the check reads quotation marks and parentheses, each letter and each digit of a text is in a word (the theorem `Runs.counted`).
- The next fact is also about the text before the check reads quotation marks and parentheses. There, a word with a letter or a digit has only letters, digits, hyphens and apostrophes (the theorem `Runs.wordy`).

The check of a definition reads the characters of the cell. It does not use md4c. For example, it reads the two backticks of a code span as punctuation, and it reads the text between them as words.

### The result of each check of a document

Each check from C1 to C8 is a Lean function in [`RegulaCore/ControlledProse.lean`](../../lean/RegulaCore/ControlledProse.lean). Each function has a decision contract, and the checker examines that contract. The contract tells that the function gives no finding for a document if, and only if, the document agrees with a statement. The statement is about the blocks of the document and about the sentences of each block.

The relations `Blocks` and `Divided` give the blocks and the sentences. The theorem `tally_zero_iff` puts the eight contracts together.

- C1 is for a paragraph, an item of an unordered list and a table cell. C2 is for an item of an ordered list, and for each such block that starts with `WARNING:` or `CAUTION:`.
- C3 is for each paragraph, and a paragraph of a list item is also a paragraph. C3 counts each sentence of the paragraph, and a sentence in parentheses is one of them.
- C4 finds each semicolon in the text that the parser gives as prose. It does not find a semicolon in code.
- C5 finds only the contractions of its definition. It does not find `'s` after a noun as a short form of a verb, and it accepts the possessive `'s`.
- C5 to C8 do not read quoted text and code.
- C6 and C7 compare words in lowercase, without the hyphens and the apostrophes at the start and at the end of a word. They find only the same letters, thus they do not find the plural of a replaced word.
- C6 and C7 accept a replaced name or a replaced word that is a part of a longer term of `CONTEXT.md`.
- C6 and C7 are about `CONTEXT.md`, not about the dictionary of ASD-STE100. The executable does not use C6 and C7 for `CONTEXT.md`, because that file must contain the replaced names and words.
- In a document, the checks read the apostrophe `’` as the apostrophe `'`.
- No check makes a decision about a rule of the dictionary. Rules 1.1 to 1.4 are in the class "reviewed".

### The result of check C9

The decisions of C9 are three Lean functions in `RegulaCore/Vocabulary.lean`. Each function has a decision contract, and the checker examines that contract.

- `parse` accepts a text if, and only if, the text is the text that `write` gives for a vocabulary (`checked_parse`). A vocabulary is a value with the statement `Draft.WellFormed`.
- `adopt` accepts two vocabularies if, and only if, three conditions are correct (`checked_adopt`). The vocabulary of the project has the line `Shared vocabulary:`. The vocabulary of the package does not have that line. The rows of the project and the `Shared` tables of the package together have `Draft.WellFormed`.
- `untracked` gives no row if, and only if, the source path of each row is in the list of tracked files of its repository (`checked_untracked`).

Each message of C9 starts with the file, the line and the check. The function `explain` gives the messages of `parse`. It gives no message if, and only if, `parse` accepts the text (the theorem `explain_nil_iff`). The theorem `clashes_nil_iff` shows the same for `clashes` and `adopt`. The controls in `lean/Fixtures/ControlledProse` examine the start of each message.

### The limits of the proofs

The contracts are about the data that the functions get. Lean does not prove these items:

- That the text of a file is the text that a function gets. The file system gives the text.
- That the lists of tracked files are correct. Git gives them.
- That the baseline of the base revision is correct. Git gives it.
- That a digest is the SHA-256 digest of a file. The `shasum` program gives it.
- That md4c and GitHub read a document with the same result.
- That the code which makes pieces from the result of md4c is correct. That code is in [`markdown/RegulaMarkdown.lean`](../../markdown/RegulaMarkdown.lean). It has controls, but no theorem.
- That the definitions of a word and of a sentence are correct for a reader.
- That the program uses the decisions in the correct sequence. That code is in [`markdown/MarkdownMain.lean`](../../markdown/MarkdownMain.lean), and the controls examine it.

## The baseline

The file [`prose-baseline.json`](../../prose-baseline.json) is the baseline. It has an entry for each document that does not obey the writing rules at this time. An entry has the path of a document and one of these three classes:

- Eight numbers: the number of findings of each check from C1 to C8. The document must have these numbers of findings, not smaller numbers and not larger numbers.
- `frozen` and a SHA-256 digest: the document is a record that must not change. The checks do not read it, and B1 does not accept a change to its text.
- `generated` and a source: a program writes the document from sources that the checks do not read. The checks do not read the document.

A document with no entry must have no finding (check B1). Check B2 compares the baseline with the baseline of the base revision. The base revision is the merge base of `HEAD` and `origin/main`. B2 does not accept a new path, a larger number or a different class. Thus the baseline can only become smaller.

B2 also does not accept the removal of a `frozen` entry while its document is a tracked file. Thus the removal of an entry does not let a frozen document change (the theorem `frozen_unchanged`).

These checks are not a check of each changed line. A change can add one finding and remove one finding in the same document, and the checks accept that change.

The decisions of the baseline are three Lean functions in [`RegulaCore/ProseBaseline.lean`](../../lean/RegulaCore/ProseBaseline.lean), each with a decision contract:

- `Baseline.parse` accepts a text if, and only if, the text is the text that `Baseline.write` gives for a baseline (`checked_baselineParse`).
- `gate` (check B1) gives no document if, and only if, the baseline admits each document (`checked_gate`). The statement is `Observed.Admitted`.
- `ratchet` (check B2) gives no entry if, and only if, the baseline shrinks in relation to the baseline of the base revision (`checked_ratchet`). The statement is `Shrinks`.

A number of the baseline is a text of decimal digits. B2 compares two numbers as such texts. A number with fewer digits is the smaller number, and two numbers with the same number of digits are compared digit by digit.

Each message of B1 and B2 starts with `prose-baseline.json`, the line of an entry and the check. For a document or a frozen entry that is not in the baseline, the line is the line where its entry would be.

Do these steps after you correct findings in a document that has an entry:

1. Go to the directory `markdown`.
2. Use the command `lake exe regula-markdown .. --write-baseline`.
3. Make sure that the baseline has only smaller numbers and no new entry.

To see each finding of one document, use the command `lake exe regula-markdown .. --list PATH` in the directory `markdown`.

## The specification of a check

Each check is a Lean function with a decision contract. The contract compares the function with a specification. These rules are for the specification of each check of these writing rules, and for each new check:

- A specification is a statement about the data that the function reads. It uses logic, the core library of Lean and the data types of the check.
- A specification can use a definition of the project only if that definition is not recursive. Such a definition only gives a name to a statement or to data.
- A specification does not call a recursive function of the project. Such a function has a theorem that connects its result with a specification.
- If Lean can make the decision from the form of a specification, the function uses the specification itself. Then the function and the specification cannot become different.
- The function `write` is the definition of the grammar of a file. The function `parse` accepts only a text that `write` gives, and a theorem shows that.

For example, the specification of a term does not call the function `split`. It tells that the term is words with one space between two words. The theorem `separated_iff` connects `split` with that specification.

The types of characters are a part of each specification, for example the list of the space characters. No theorem shows that they are correct. A change to them is a change to the specification.

## Writing rules with a review

A check cannot make a decision about the other writing rules, because they are about the part of speech or the meaning of a word. A reviewer reads the text and ASD-STE100 for these rules:

- Words: rules 1.1 to 1.7, 1.9, 1.10, 1.12 to 1.14, and 9.1 to 9.3.
- Nouns: rules 2.1 and 2.2.
- Verbs: rules 3.1 to 3.7.
- Sentences and lists: rules 4.1 to 4.5.
- Procedures: rules 5.2 to 5.5.
- Descriptions: rules 6.1, 6.2, 6.4 and 6.5.
- Safety instructions: rules 7.1 to 7.3.
- Punctuation: rules 8.2 and 8.3.
- Style: rule 9.4.

Use a word that the dictionary of ASD-STE100 gives as approved, with its approved part of speech and its approved meaning. A different word is permitted only as a technical noun or as a technical verb (rules 1.5 and 1.12). For an item that has a name in `CONTEXT.md`, use that name.

The procedure of the review is in the [controlled-language review](../../.agents/skills/pr-review-toolkit/references/controlled-language-lens.md) of the review skill.

## How to write about compliance

Use two classes, and give the commit:

- "Enforced by a check" for the checks C1 to C9.
- "Reviewed" for the other writing rules, with the rule numbers and the name of the reviewer.

Do not write "certified" or "approved by ASD" about a document. Do not write "ASD-STE100 compliant" without the two classes.

## A new term

Add a row to `CONTEXT.md` in the same pull request as the text that uses the term. A row is for the name of an item of the project or of Lean. The row gives these items:

- The term: a noun or a verb of one, two or three words.
- The category of rule 1.5 for a noun, or of rule 1.12 for a verb.
- One sentence of definition.
- The names that the term replaces.
- The tracked file that gives the definition of the term, and the Lean name if there is one.

The record of the review in the pull request gives the result of the dictionary check of the term. For a verb, the record also gives the approved verb that the writer tried first.

## Text that these writing rules do not change

The writing rules do not change these types of text:

- Code, identifiers and program output.
- Text that a different source wrote, in quotation marks or in a block quote.
- A record that must not change, for example a registered protocol and its results.
- The uppercase requirement keywords of the Regula standard.

The checks read a block quote and a paragraph with the same procedure. If the text of a different source has a finding, put it in quotation marks or in a code block.
