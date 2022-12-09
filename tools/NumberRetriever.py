class NumberRetriever():
	
	def __init__(self):
		self.linecounts = [0]

	def process_line(self, original_line_number, expand_size):
		#print("Process Line:", original_line_number, expand_size)
		self.linecounts.append(self.linecounts[-1] + expand_size)

	def get_reference(self, original_clause):
		#print("Find original: ", original_clause, len(self.linecounts))
		ans =  self.linecounts[original_clause]
		#print("Found: ", ans)
		return ans
