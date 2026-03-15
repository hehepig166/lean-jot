Chceck if there is a file called test.txt in the target folder.

if not, create the file (empty), and print "END_REASON:SELECTED_TARGET_COMPLETE" in the very last line of your response.

If it exists, check if all the statements below are in the file.
['chinese remainder theorem', 'fermats little theorem', '1 + 1 = 2']

if not all of them are in the file, choose EXACTLY ONE of the statements that is not in the file, and use 'leandex' to search it in mathlib, and add the result to the file. Then print "END_REASON:LIMIT" in the very last line of your response.

if all of them are in the file, print "END_REASON:COMPLETE" in the very last line of your response.

VERY IMPORTANT: The last line of your output should not contain any other text or markdown formatting.