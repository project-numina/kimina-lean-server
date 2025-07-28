# import re
# from typing import Optional


# def extract_nodes_and_edges(
#     infotree: list[dict],
#     parent_id: Optional[int] = None,
#     start_id: int = 0,
#     include_failed_pp: bool = True,
#     deduplicate: bool = False,
# ):
#     """
#     Recursively extract nodes and edges from an infotree.

#     Parameters
#     ----------
#     infotree : list of dict
#         A list of dictionaries each containing 'node' and optionally 'children'.
#     parent_id : int or None, optional
#         The ID of the parent node, or None if this is the root level (default is None).
#     start_id : int, optional
#         The next available integer ID to assign to a new node (default is 0).
#     include_failed_pp : bool, optional
#         If False, nodes whose pretty-print text is "<failed to pretty print>" are removed
#         (default is True).
#     deduplicate : bool, optional
#         If True, deduplicate chains of identical nodes based on goalsBefore,
#         goalsAfter, and pp (default is False).

#     Returns
#     -------
#     nodes : dict[int, dict]
#         A dictionary of node_id -> node_content.
#     edges : list[tuple[int, int, dict]]
#         A list of tuples (parent_id, child_id, {}) representing edges in the infotree.
#     next_id : int
#         The next available integer ID after processing all children.
#     """
#     nodes = {}
#     edges = []

#     current_id = start_id

#     for item in infotree:
#         if "node" in item:
#             node_data = item["node"]

#             # Add this node to the nodes dictionary
#             node_id = current_id
#             current_id += 1
#             nodes[node_id] = node_data

#             # Recursively handle the children of the node, depth-first approach
#             if (
#                 "children" in item
#                 and isinstance(item["children"], list)
#                 and item["children"]
#             ):
#                 child_nodes, child_edges, current_id = extract_nodes_and_edges(
#                     item["children"],
#                     parent_id=node_id,
#                     start_id=current_id,
#                     include_failed_pp=include_failed_pp,
#                     deduplicate=deduplicate,
#                 )
#                 nodes.update(child_nodes)
#                 edges.extend(child_edges)

#             # Add an edge from the parent to this node
#             if parent_id is not None:
#                 edges.append((parent_id, node_id, {}))

#             # Now handle possible flattening in a loop until there are no more changes
#             transformed = True
#             while transformed:
#                 transformed = False

#                 # 1) Remove/flatten all children that have failed PP (if include_failed_pp=False)
#                 #    We handle them individually, even if there's more than one child.
#                 #    Then we break to re-check children from scratch, as new failed PP children might appear.
#                 child_list = [
#                     e for e in edges if e[0] == node_id
#                 ]  # edges from node_id to child
#                 for edge_obj in child_list:
#                     child_id = edge_obj[1]
#                     child_content = nodes.get(child_id, {})
#                     child_pp = child_content.get("stx", {}).get("pp", "")

#                     if not include_failed_pp and child_pp == "<failed to pretty print>":
#                         # Flatten this child: remove it and connect parent directly to its children
#                         # Note that the new children might also have failed PP, so we need to re-check them
#                         _flatten_chain(nodes, edges, node_id, child_id)
#                         transformed = True
#                         break

#                 if transformed:
#                     # We need to restart the while loop to re-check children from scratch, as there might be
#                     # more failed PP children
#                     continue

#                 # 2) Deduplicate if there's exactly one child left that has same (goalsBefore, goalsAfter, pp)
#                 # This happens quite often in infotrees, where a tactic is repeated multiple times, extracted
#                 # with different parsers
#                 child_list = [e for e in edges if e[0] == node_id]
#                 if deduplicate and len(child_list) == 1:
#                     child_id = child_list[0][1]
#                     if child_id in nodes:
#                         child_content = nodes[child_id]
#                         # Compare parent's vs child's (goalsBefore, goalsAfter, pp)
#                         parent_goalsBefore = node_data.get("goalsBefore", [])
#                         parent_goalsAfter = node_data.get("goalsAfter", [])
#                         parent_pp = node_data.get("stx", {}).get("pp", "")

#                         child_goalsBefore = child_content.get("goalsBefore", [])
#                         child_goalsAfter = child_content.get("goalsAfter", [])
#                         child_pp = child_content.get("stx", {}).get("pp", "")

#                         if (
#                             child_goalsBefore == parent_goalsBefore
#                             and child_goalsAfter == parent_goalsAfter
#                             and child_pp == parent_pp
#                         ):
#                             # Flatten this child: remove it and connect parent directly to its children
#                             _flatten_chain(nodes, edges, node_id, child_id)
#                             transformed = True

#         else:
#             # If the item does not contain a 'node' key but might have children
#             if "children" in item and isinstance(item["children"], list):
#                 child_nodes, child_edges, current_id = extract_nodes_and_edges(
#                     item["children"],
#                     parent_id=parent_id,
#                     start_id=current_id,
#                     include_failed_pp=include_failed_pp,
#                     deduplicate=deduplicate,
#                 )
#                 nodes.update(child_nodes)
#                 edges.extend(child_edges)

#     return nodes, edges, current_id


# def _flatten_chain(nodes: dict, edges: list[tuple], parent_id: int, child_id: int):
#     """
#     Flatten a chain by removing 'child_id' node and connecting 'parent_id'
#     directly to the child's children.
#     Given a parent node that has a single child, this function removes the child
#     node from the dictionary of nodes and reassigns the child's children to the parent.
#     This is used for node deduplication and removing failed-pp nodes.

#     Parameters
#     ----------
#     nodes : dict[int, dict]
#         A dictionary of node_id -> node_content.
#     edges : list[tuple[int, int, dict]]
#         A list of tuples (parent_id, child_id, {}) representing edges in the infotree.
#     parent_id : int
#         The ID of the parent node.
#     child_id : int
#         The ID of the child node that should be removed.

#     Returns
#     -------
#     None
#         This function modifies the nodes and edges in place.
#     """
#     if child_id not in nodes:
#         return

#     # Remove the node from the dictionary
#     del nodes[child_id]

#     # Remove edge from parent_id -> child_id
#     edges[:] = [e for e in edges if not (e[0] == parent_id and e[1] == child_id)]

#     # Reassign child's children edges to the parent
#     for i, (src, tgt, attr) in enumerate(edges):
#         if src == child_id:
#             edges[i] = (parent_id, tgt, attr)


# def get_intervals(nodes: dict) -> list[dict]:
#     """
#     Build a list of intervals from a given nodes dictionary.
#     Each interval represents a tactic in the Lean file, capturing its
#     start and finish positions, as well as the associated goals.

#     Parameters
#     ----------
#     nodes : dict of {int : dict}
#         A dictionary of node_id -> node_content.

#     Returns
#     -------
#     intervals : list of dict
#         A list of dictionaries, each containing:
#           node_id, pp, start_line, start_col, finish_line, finish_col, goalsBefore, goalsAfter
#     """
#     intervals = []
#     for node_id, node_content in nodes.items():
#         stx_range = node_content.get("stx", {}).get("range", {})
#         start_dict = stx_range.get("start", {})
#         finish_dict = stx_range.get("finish", {})

#         intervals.append(
#             {
#                 "node_id": node_id,
#                 "pp": node_content.get("stx", {}).get("pp", ""),
#                 "start_line": start_dict.get("line", 0),
#                 "start_col": start_dict.get("column", 0),
#                 "finish_line": finish_dict.get("line", 0),
#                 "finish_col": finish_dict.get("column", 0),
#                 "goalsBefore": node_content.get("goalsBefore", []),
#                 "goalsAfter": node_content.get("goalsAfter", []),
#             }
#         )
#     return intervals


# def adjust_intervals(intervals: list[dict]) -> list[dict]:
#     """
#     Make intervals disjoint and create a file partition.
#     Sort intervals by starting position, then set each interval's end to the next
#     interval's start. This creates a sequence of adjacent intervals covering the file.

#     Parameters
#     ----------
#     intervals : list of dict
#         A list of dictionaries, each containing:
#           node_id, pp, start_line, start_col, finish_line, finish_col, goalsBefore, goalsAfter

#     Returns
#     -------
#     intervals_sorted : list of dict
#         The updated intervals, sorted and trimmed so that they do not overlap.
#     """
#     intervals_sorted = sorted(
#         intervals, key=lambda iv: (iv["start_line"], iv["start_col"])
#     )

#     # Remember the furthest original finish position
#     max_finish_line, max_finish_col = -1, -1
#     for iv in intervals_sorted:
#         if (iv["finish_line"], iv["finish_col"]) > (max_finish_line, max_finish_col):
#             max_finish_line, max_finish_col = iv["finish_line"], iv["finish_col"]

#     for i in range(len(intervals_sorted) - 1):
#         current = intervals_sorted[i]
#         nxt = intervals_sorted[i + 1]
#         current["finish_line"] = nxt["start_line"]
#         current["finish_col"] = nxt["start_col"]
#         current["goalsAfter"] = nxt["goalsBefore"]

#     if intervals_sorted:
#         intervals_sorted[-1]["finish_line"] = max_finish_line
#         intervals_sorted[-1]["finish_col"] = max_finish_col

#     intervals_sorted = [
#         iv
#         for iv in intervals_sorted
#         if not (
#             iv["start_line"] == iv["finish_line"]
#             and iv["start_col"] == iv["finish_col"]
#         )
#     ]

#     return intervals_sorted


# def retrieve_tactics(intervals: list[dict], source_lines: list[str]) -> list[dict]:
#     """
#     Extract tactic code snippets from source lines based on intervals.

#     Parameters
#     ----------
#     intervals : list of dict
#         A list of dictionaries, each containing:
#           node_id, pp, start_line, start_col, finish_line, finish_col, goalsBefore, goalsAfter
#         Note: At this point, the pp field does not exactly correspond to the positions.
#     source_lines : list of str
#         The lines of the Lean file, read into a list.

#     Returns
#     -------
#     results : list of dict
#         A list of intervals augmented with the 'tactic' text from the file.
#         Each dict has keys: goalsBefore, goalsAfter, tactic.
#     """
#     results = []
#     for i in range(len(intervals)):
#         iv = intervals[i]
#         snippet_text = _extract_snippet(
#             source_lines,
#             iv["start_line"],
#             iv["start_col"],
#             iv["finish_line"],
#             iv["finish_col"],
#         )
#         data = {
#             "goalsBefore": iv["goalsBefore"],
#             "goalsAfter": iv["goalsAfter"],
#             "tactic": snippet_text,
#         }
#         results.append(data)

#     return results


# def _extract_snippet(
#     source_lines: list[str],
#     start_line: int,
#     start_col: int,
#     finish_line: int,
#     finish_col: int,
# ) -> str:
#     """
#     Extract a code snippet from the Lean source lines.

#     Given a start and finish line-column pair, slice the lines to produce the exact text
#     range in the Lean file. This handles both single-line and multi-line cases.

#     Parameters
#     ----------
#     source_lines : list of str
#         The lines read from the Lean file.
#     start_line : int
#         The 1-based starting line index.
#     start_col : int
#         The 0-based starting column index within start_line.
#     finish_line : int
#         The 1-based finishing line index.
#     finish_col : int
#         The 0-based finishing column index within finish_line.

#     Returns
#     -------
#     str
#         The extracted snippet from the Lean file, spanning (start_line, start_col)
#         to (finish_line, finish_col).
#     """
#     # Single line case
#     if start_line == finish_line:
#         line_idx = start_line - 1
#         line_text = source_lines[line_idx]
#         return line_text[start_col:finish_col]

#     # Multi-line case
#     # 1) from start_col to end-of-line for start_line
#     snippet_parts = []
#     start_line_idx = start_line - 1
#     line_text = source_lines[start_line_idx]
#     snippet_parts.append(line_text[start_col:])

#     # 2) full lines between (start_line+1) .. (finish_line-1)
#     for line_idx in range(start_line_idx + 1, finish_line - 1):
#         snippet_parts.append(source_lines[line_idx])

#     # 3) from begin-of-line up to finish_col for finish_line
#     last_line_idx = finish_line - 1
#     last_line = source_lines[last_line_idx]
#     snippet_parts.append(last_line[:finish_col])

#     return "".join(snippet_parts)


# def separate_trailing_whitespace(s: str) -> tuple[str, str]:
#     """
#     Remove trailing whitespace from a tactic and return (code, trailing_ws).

#     Example:
#     - Input: "have h1 : ... := by\n    "
#     - Output: ("have h1 : ... := by", "\n    ")

#     Parameters
#     ----------
#     s : str
#         A tactic string (Lean4 code).

#     Returns
#     -------
#     code : str
#         The tactic string without potential whitespaces at the end.
#     trailing_ws : str
#         The whitespaces at the end of s. Potentially None.
#     """
#     code = s.rstrip(" \t\n\r")
#     trailing_ws = s[len(code) :]
#     return code, trailing_ws


# def separate_trailing_comment(s: str) -> tuple[str, str]:
#     """
#     Remove trailing comments only if they start at the beginning of the line
#     (modulo whitespace). Return (clean, trailing_comment).

#     A trailing comment can be:
#       - One or more single-line comments (lines starting with '--').
#       - One multi-line block comment starting with '/-' (at line start, ignoring whitespace)
#         and ending somewhere before the end of the string (must contain '-/').

#     Example:
#     - Input: "have h1 : ... := by\n  -- To prove this have statement, we will just apply mul_pos"
#     - Output: ("have h1 : ... := by\n  ", "-- To prove this have statement, we will just apply mul_pos")

#     Note that the function does not extract trailing whitespaces from the tactic right before the start of the comment.

#     Parameters
#     ----------
#     s : str
#         A tactic string (Lean4 code).

#     Returns
#     -------
#     clean : str
#         The tactic string without potential comments at the end.
#     comment : str
#         The comment at the end of s. Potentially None.
#     """
#     lines = s.splitlines(keepends=True)

#     # If no lines, do nothing
#     if not lines:
#         return s, ""

#     trailing_comments = []  # This will contain all the trailing comments
#     i = len(lines) - 1  # Start from the end of the file

#     while i >= 0:
#         line = lines[i]

#         # 1. If the line is blank, add it to the trailing_comments and go to the next line
#         if line.strip() == "":
#             trailing_comments.append(line)
#             i -= 1
#             continue

#         # 2. Check if the line ends a multi-line block comment (i.e., has '-/'):
#         if "-/" in line:
#             end_idx = i
#             start_idx = end_idx
#             # Move upward until we find a line that starts with '/-' (mod whitespace)
#             while start_idx >= 0 and not re.match(r"^\s*/-", lines[start_idx]):
#                 start_idx -= 1
#             if start_idx < 0:
#                 # Found '-/' but no valid start => not truly trailing
#                 break
#             # Everything from start_idx..end_idx is the trailing block comment
#             block_str = "".join(lines[start_idx : end_idx + 1])
#             trailing_comments.append(block_str)
#             i = start_idx - 1  # jump above the block
#             continue

#         # 3. Check if the line is a single-line comment
#         if re.match(r"^\s*--", line) is not None:
#             trailing_comments.append(line)
#             i -= 1
#             continue

#         # 4. If none of the above, then we’ve hit a real line of code
#         break

#     clean_code = "".join(lines[: i + 1])

#     # If we didn't find any trailing comment, return the code with an empty string
#     if trailing_comments == []:
#         return clean_code, ""

#     else:
#         trailing_comments.reverse()  # trailing_comments is in bottom-to-top order, reverse it to restore top-to-bottom
#         trailing_comments = "".join(trailing_comments)
#         return clean_code, trailing_comments


# def transfer_trailing_whitespaces_and_comments(intervals: list[dict]):
#     """
#     For each tactic in 'intervals' (except the last), remove trailing whitespaces,
#     then trailing comments (if any), then trailing whitespaces again,
#     and prepend all that to the next interval.

#     Parameters
#     ----------
#     intervals : list of dict
#         A list of dictionaries, each containing:
#           goalsBefore, goalsAfter, tactic.

#     Returns
#     -------
#     None
#         The 'tactic' fields in intervals are modified in place.
#     """
#     for i in range(len(intervals) - 1):
#         current = intervals[i]
#         nxt = intervals[i + 1]

#         # 1) Remove trailing whitespace
#         code, trailing_ws_1 = separate_trailing_whitespace(current["tactic"])

#         # 2) Remove trailing comment
#         code, trailing_comment = separate_trailing_comment(code)

#         # 3) Remove trailing whitespace again
#         code, trailing_ws_2 = separate_trailing_whitespace(code)

#         # Update the current tactic
#         current["tactic"] = code

#         # Prepend to the next interval
#         nxt["tactic"] = trailing_ws_2 + trailing_comment + trailing_ws_1 + nxt["tactic"]


# def remove_lean_comments(text) -> str:
#     """
#     Remove single-line and multi-line comments from `text`.

#     Parameters
#     ----------
#     text : str
#         The Lean code that may contain comments.

#     Returns
#     -------
#     text : str
#         The Lean code without comments.
#     """
#     # First, remove all multi-line comments
#     pattern = re.compile(r"/-.*?-/", re.DOTALL)
#     text = pattern.sub("", text)

#     # Then, remove all single-line comments
#     lines = text.splitlines()
#     new_lines = []
#     for line in lines:
#         if line.strip() == "":
#             new_lines.append(line)
#             continue
#         if "--" in line:
#             # Keep only the part before the first occurrence of "--"
#             line = line.split("--")[0].rstrip()
#         if line.strip() != "":
#             new_lines.append(line)
#     text = "\n".join(new_lines)

#     return text


# def is_balanced(tactic: str) -> bool:
#     """
#     Check whether `[]`, `()` and `⟨⟩` are balanced in `tactic`.

#     Parameters
#     ----------
#     tactic : str
#         A Lean tactic snippet.

#     Returns
#     -------
#     bool
#         True if every opening bracket/parenthesis is matched by its closing counterpart, False otherwise.
#     """
#     return (
#         tactic.count("[") == tactic.count("]")
#         and (tactic.count("(") == tactic.count(")"))
#         and (tactic.count("⟨") == tactic.count("⟩"))
#     )


# def is_by(tactic: str) -> bool:
#     """
#     Check whether the tactic is exactly the keyword `by`.
#     Comments are removed and surrounding whitespace is ignored before the comparison.

#     Parameters
#     ----------
#     tactic : str
#         A Lean tactic snippet.

#     Returns
#     -------
#     bool
#         True if the tactic is a 'by', False otherwise.
#     """
#     return remove_lean_comments(tactic).strip() == "by"


# def is_calc(tactic: str) -> bool:
#     """
#     Check whether the snippet introduces a `calc` block.
#     Accepted forms are either `calc` or `by calc`.

#     Parameters
#     ----------
#     tactic : str
#         A Lean tactic snippet.

#     Returns
#     -------
#     bool
#         True if the tactic introduces a `calc` block, False otherwise.
#     """
#     s = remove_lean_comments(tactic).strip()
#     # Direct match
#     if s == "calc":
#         return True
#     # Match `by calc` with spaces or newlines after `by`
#     m = re.match(r"^by\s+([\w_]+)$", s)
#     return bool(m and m.group(1) == "calc")


# WRAPPER_TACTICS: set[str] = {
#     "all_goals",
#     "any_goals",
#     "repeat",
# }


# def is_wrapper(tactic: str) -> bool:
#     """
#     Check whether the tactic is a wrapper tactic (e.g., `all_goals`, `any_goals`, `repeat`),
#     optionally preceded by `by`.

#     Parameters
#     ----------
#     tactic : str
#         A Lean tactic snippet.

#     Returns
#     -------
#     bool
#         True if the tactic is a wrapper tactic, False otherwise.
#     """
#     s = remove_lean_comments(tactic).strip()
#     # Direct match
#     if s in WRAPPER_TACTICS:
#         return True
#     # Match `by <wrapper>` with spaces or newlines after `by`
#     m = re.match(r"^by\s+([\w_]+)$", s)
#     return bool(m and m.group(1) in WRAPPER_TACTICS)


# def ends_with_by(tactic: str) -> bool:
#     """
#     Check whether the tactic ends with `:= by` or `:=by`, ignoring trailing comments and whitespace.

#     Parameters
#     ----------
#     tactic : str
#         A Lean tactic snippet.

#     Returns
#     -------
#     bool
#         True if the tactic ends with `:= by` or `:=by`, False otherwise.
#     """
#     s = remove_lean_comments(tactic).rstrip()
#     return s.endswith(":=by") or s.endswith(":= by")


# def merge_intervals(intervals: list[dict]) -> list[dict]:
#     """
#     Merge intervals that are not balanced or contain specific tactics.

#     Parameters
#     ----------
#     intervals : list of dict
#         A list of dictionaries, each containing:
#           goalsBefore, goalsAfter, tactic.

#     Returns
#     -------
#     merged_intervals : list of dict
#         A list of dictionaries, each containing:
#           goalsBefore, goalsAfter, tactic.
#         The tactics that do not change the goals are merged with their successor.
#     """
#     merged_intervals = []
#     i = 0
#     while i < len(intervals):
#         accumulated = intervals[i]["tactic"]
#         j = i + 1
#         # Merge subsequent intervals until accumulated tactic is balanced.
#         while j < len(intervals) and (
#             not is_balanced(accumulated)
#             or is_by(accumulated)
#             or is_calc(accumulated)
#             or is_wrapper(accumulated)
#         ):
#             accumulated += intervals[j]["tactic"]
#             j += 1

#         merged_interval = {
#             "goalsBefore": intervals[i]["goalsBefore"],
#             "goalsAfter": intervals[j - 1]["goalsAfter"],
#             "tactic": accumulated,
#         }

#         merged_intervals.append(merged_interval)
#         i = j

#     # Transfer trailing `by`
#     for k in range(len(merged_intervals) - 1):
#         if ends_with_by(merged_intervals[k]["tactic"]):
#             txt = merged_intervals[k]["tactic"]
#             cut = txt.rfind(":=") + 2  # keep the ':='
#             by_part = txt[cut:]  # 'by' or ' by', incl. space
#             merged_intervals[k]["tactic"] = txt[:cut]
#             merged_intervals[k + 1]["tactic"] = (
#                 by_part + merged_intervals[k + 1]["tactic"]
#             )

#     # Set goalsBefore of tactic n to be the first non-empty goalsBefore starting at n.
#     for i in range(len(merged_intervals) - 1):
#         new_goals = []
#         for j in range(i, len(merged_intervals)):
#             if merged_intervals[j]["goalsBefore"] != []:
#                 new_goals = merged_intervals[j]["goalsBefore"]
#                 break
#         merged_intervals[i]["goalsBefore"] = new_goals

#     # Set goalsAfter of tactic n to be the goalsBefore of tactic n+1.
#     for i in range(len(merged_intervals) - 1):
#         new_goals = []
#         for j in range(i + 1, len(merged_intervals)):
#             if merged_intervals[j]["goalsBefore"] != []:
#                 new_goals = merged_intervals[j]["goalsBefore"]
#                 break
#         merged_intervals[i]["goalsAfter"] = new_goals

#     return merged_intervals


# def extract_data(infotree: list[dict], source_code: str) -> list[dict]:
#     """
#     Performs the whole extraction process from an infotree and the corresponding Lean4 code.

#     This function:
#       - Extracts nodes and edges from the infotree,
#       - Removes synthetic nodes,
#       - Builds and adjusts intervals to partition the Lean4 code,
#       - Retrieves tactics from the Lean4 code,
#       - Transfers trailing whitespaces and comments between consecutive tactics,
#       - Merge intervals that are not balanced or contain specific tactics.

#     Parameters
#     ----------
#     infotree : list of dict
#         A list of dictionaries each containing 'node' and optionally 'children'.
#     source_code : str
#         The Lean4 code for retrieving text snippets.

#     Returns
#     -------
#     intervals : list of dict
#         A list of dictionaries, each containing:
#           goalsBefore, goalsAfter, tactic.
#         The intervals are partitioned and cover the whole file.
#     """
#     # 1. Extract nodes and edges
#     nodes, _, _ = extract_nodes_and_edges(
#         infotree, include_failed_pp=False, deduplicate=True
#     )

#     # 2. Filter out the synthetic nodes
#     nodes = {
#         k: v
#         for k, v in nodes.items()
#         if not v.get("stx", {}).get("range", {}).get("synthetic", False)
#     }

#     # 3. Build raw intervals from nodes
#     intervals = get_intervals(nodes)

#     # 4. Adjust intervals so they become disjoint and partition the proof
#     intervals = adjust_intervals(intervals)

#     # 5. Load lines from the Lean file
#     source_lines = source_code.split("\n")
#     source_lines = [line + "\n" for line in source_lines[:-1]] + [source_lines[-1]]

#     # 6. Extract the tactic for each final interval
#     intervals = retrieve_tactics(intervals, source_lines)

#     # 7. Transfer trailing whitespaces and comments
#     transfer_trailing_whitespaces_and_comments(intervals)

#     # 8. Merge intervals that are not balanced or contain specific tactics
#     intervals = merge_intervals(intervals)

#     return intervals
