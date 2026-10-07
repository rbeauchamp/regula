# Controlled-language review

Use this procedure for a pull request that adds or changes prose in a Markdown document. The [writing rules](../../../../docs/guides/writing.md) give the rules that a check examines and the rules that a reviewer examines. A person or an agent can be the reviewer.

## How to read ASD-STE100

1. Use a copy of ASD-STE100 from ASD.
2. Do not put the copy in the repository.
3. Read the necessary pages. An agent uses the Read tool with a page range.
4. Read a rule before you use it.
5. Read the dictionary entry of a word before you give a result for the word.
6. Do not use a program that gets the text from the copy.
7. Do not keep pages or images of pages.
8. Do not write text of ASD-STE100 in a file, a prompt, an issue or a comment.
9. Write a rule as its number, and write a dictionary word as the word only.

Step 8 is for each sentence, each example and each approved meaning of ASD-STE100.

## The text that the reviewer examines

Examine the changed prose for each writing rule of the class "reviewed". Read the dictionary entry of each word that is not in `CONTEXT.md`, if you are not sure that the word is approved.

Examine each new row of `CONTEXT.md`:

- The term agrees with its category of rule 1.5 or rule 1.12.
- The definition agrees with the source of the row.
- For a verb, no approved verb gives the same meaning.

## The record of the review

Write a block "Controlled-language review" in the description of the pull request. The block gives these items:

- The commit, the files and the edition ("ASD-STE100 Issue 9").
- The rule numbers that the reviewer used.
- Each finding: the file and the line, the rule number, the problem in the words of the reviewer, and the new text.
- Each dictionary check: the word, the result and the decision.
- That the reviewer read ASD-STE100 and did not get its text with a program.
- The result of the review: each finding is corrected, or the document has an entry in the baseline and the record gives the cause.

The result of a dictionary check is one of these: approved with a part of speech, not approved, or not in the dictionary. The decision is one of these: keep the word, replace it with a different word, or add a term to `CONTEXT.md` with a category.

## The limits of the review

The review shows that one reviewer read the changed text and compared it with the rules of the record at one commit. It is not a proof. A different reviewer can give a different result for a rule about the meaning of a word.
