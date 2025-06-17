def generate_penta_cases():
    #really inefficient, but it works
    with open("plist.txt", "r") as f:
        for line in f:
            (res, eq) = line.strip().split(" = ")
            res = int(res)
            
            nums = [0, 0, 0, 0]
            if eq.count("+") == 0:
                nums[0] = int(eq)
            else:
                eq = eq.split(" + ")
                nums = list(map(int, eq))
                for _ in range(4 - len(nums)):
                    nums.append(0)
            
            print(f"      . simp; use {nums}; simp [p{nums[0]}, p{nums[1]}, p{nums[2]}, p{nums[3]}]")

def generate_hexa_cases():
    #really inefficient, but it works
    with open("hlist.txt", "r") as f:
        for line in f:
            (res, eq) = line.strip().split(" = ")
            res = int(res)
            
            nums = [0, 0, 0, 0, 0]
            if eq.count("+") == 0:
                nums[0] = int(eq)
            else:
                eq = eq.split(" + ")
                nums = list(map(int, eq))
                for _ in range(5 - len(nums)):
                    nums.append(0)
            
            print(f"      . simp; use {nums}; simp [h{nums[0]}, h{nums[1]}, h{nums[2]}, h{nums[3]}, h{nums[4]}]")

if __name__ == "__main__":
    generate_hexa_cases()