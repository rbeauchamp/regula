# Writing rules

Obey the writing rules of ASD-STE100 Simplified Technical English, Issue 9 (January 2025), when you write or change a Markdown document of this repository. ASD-STE100 is a document of the Aerospace, Security and Defence Industries Association of Europe (ASD). This repository contains no part of that document. To read ASD-STE100, get a copy from ASD.

ASD-STE100 is a registered trademark of ASD. This project uses the name only to identify that document. ASD did not examine this project and gave no approval to it.

These writing rules are for the documents of this repository. They are not a part of the Regula standard, and the checker does not use them for a project that uses Regula. The check of these writing rules is a check of the repository. It is the same type of check as the check of rule IDs in documents, and it has no rule ID.

The vocabulary of the project is [`CONTEXT.md`](../../CONTEXT.md). It gives the technical nouns and the technical verbs of the project. Rule 1.5 and rule 1.12 of ASD-STE100 let a project have such words.

## Writing rules with a check

The command `./scripts/verify.sh docs` does the check of each tracked Markdown document. The check has nine parts.

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
| C9 | The format | A `CONTEXT.md` that is not the text of a vocabulary. |

### How the check reads a document

The check does not read Markdown syntax. The md4c parser reads each document in the GitHub dialect, and the check reads the blocks that the parser gives. A block is a heading, a paragraph, a paragraph of a list item or a table cell. A code block has no text for the check. The description of an image is text of its block.

The check does not read code. Put each identifier, path, command and program output in code font. A code span is one word in the count.

These definitions are the definitions of the check:

- A word is a sequence of ASCII letters and digits. A hyphen or an apostrophe between two of them continues the word (rule 8.7). A period or a comma between two digits continues the word.
- A character that is not ASCII is one word. But the check reads some characters as punctuation or as a space: two apostrophes, the quotation marks, two dashes, the ellipsis and the usual spaces.
- Text between two double quotation marks in one block is one word. The check does not read the words in it.
- Text between two parentheses in one block is one word of its sentence. The check also reads this text as one or more sentences (rule 8.5).
- A sentence stops at a period, a question mark or an exclamation mark. But a space and a new sentence must be after that mark.
- A new sentence starts with an uppercase letter, a digit, a code span, a quotation or a parenthesis.
- A sentence also stops at the end of its block. Thus the text before a list and each list item are different sentences (rule 8.4).
- A heading has no sentence.

To let the check find each sentence, start a sentence with an uppercase letter or with a code span. Do not write an abbreviation that has a period at its end.

### The result of each check

Each check is a Lean function in [`RegulaCore/ControlledProse.lean`](../../lean/RegulaCore/ControlledProse.lean) or in [`RegulaCore/Vocabulary.lean`](../../lean/RegulaCore/Vocabulary.lean). Each function has a decision contract, and the checker examines that contract. The contract tells that the function gives no finding for a document if, and only if, the document agrees with the definition of the check. The contract is about the result of the parser, not about the bytes of the file.

- C1 and C2 add one to the count for each word of a title or of a proper noun. ASD-STE100 gives one word to such a group (rule 8.6). Thus the count of the check is not smaller than the count of ASD-STE100, if the sentences are correct. The check gives two words to a number with its unit.
- The sentences of the check are the sentences of a reader only if no abbreviation with a period is before an uppercase word. C8 does not accept five such abbreviations, and the reviewer examines the others. An incorrect sentence end can make the count of C1 and C2 too small.
- C3 gives the number of the sentences of the check that are not in parentheses.
- C4 finds each semicolon in the text that the parser gives as prose. It does not find a semicolon in code.
- C5 finds only the contractions of its definition. It does not find `'s` with the meaning "is" after a noun, and it accepts the possessive `'s`.
- C6 and C7 compare words in lowercase. They find only the same letters, thus they do not find the plural of a replaced word. They accept a replaced name or a replaced word that is a part of a longer term of `CONTEXT.md`.
- C6 and C7 are about `CONTEXT.md`, not about the dictionary of ASD-STE100. The check does not use C6 and C7 for `CONTEXT.md`, because that file must contain the replaced names and words.
- C9 accepts a `CONTEXT.md` only if it is the one text that the function `write` gives for its vocabulary. C9 also does not accept a source path that is not a tracked file.
- No check makes a decision about a rule of the dictionary. Rules 1.1 to 1.4 are in the class "reviewed".

### The limits of the proofs

The proofs do not show these items:

- That md4c and GitHub read a document with the same result.
- That the code which makes blocks from the result of md4c is correct. That code is in [`markdown/RegulaMarkdown.lean`](../../markdown/RegulaMarkdown.lean). It has controls, but no theorem.
- That the list of tracked files and the baseline of the base revision are correct. Git gives them.
- That the contents of a file and its SHA-256 digest are correct. The file system and the `shasum` program give them.

## The baseline

The file [`prose-baseline.json`](../../prose-baseline.json) is the baseline. It contains an entry for each document that does not obey the writing rules at this time. An entry has the path of a document and one of these three classes:

- Eight numbers: the number of findings of each check from C1 to C8. The document must have these numbers of findings, not smaller numbers and not larger numbers.
- `frozen` and a SHA-256 digest: the document is a record that must not change. The check does not read it, and the check does not accept a change to its contents.
- `generated` and a source: a program writes the document from sources that the check does not read. The check does not read the document.

A document with no entry must have no finding. The check also compares the baseline with the baseline of the base revision. The base revision is the merge base of `HEAD` and `origin/main`. The check does not accept a new path, a larger number or a different class. Thus the baseline can only become smaller.

This check is not a check of each changed line. A change can add one finding and remove one finding in the same document, and the check accepts that change.

Do these steps after you correct findings in a document that has an entry:

1. Go to the directory `markdown`.
2. Use the command `lake exe regula-markdown .. --write-baseline`.
3. Make sure that the baseline has only smaller numbers and no new entry.

To see each finding of one document, use the command `lake exe regula-markdown .. --list PATH` in the directory `markdown`.

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

The check reads a block quote and a paragraph with the same procedure. If the text of a different source has a finding, put it in quotation marks or in a code block.
