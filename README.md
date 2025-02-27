# 04-Types
Homework assignment 4 for CSE 230

## Installation 
You do not have to install lean to do this assignment. Instead, you can use Github Codespaces to do the assignment with VSCode in your browser using an environment we have already set up. You can create a codespace by selecting (Code -> Create codespace). After that, you can use the same codespace across sessions of completing the assignment. When creating the codespace, please allow 1-2 minutes for the codespace to finish setting up, and 1-2 minutes for the lean language server to start.  


## Instructions
Follow the instructions in [Types.lean](Types.lean) to complete definitions and proofs that are currently completed using `sorry`. 


## Grading
At any point, you may check your progress by running 
```
make grade
```

## Extra Credit 
The following theorems are extra credit: 
com0_ok (30pts)
com_preservation_c (30pts)
com_preservation_s (30pts)
eval_bool (30pts)
com_progress (30pts)
checkCom (30pts)
checkCom_sound (30pts)

This means that the assignment is 270 points, and there are 210 points of extra credit. 


## Submitting
You can submit the assignment by running
```
make turnin
```
You may submit as often as you like. We will grade the latest submission at the assignment due date. 


## Research
During this quarter we will collect fine-grained information of edits you make to the `.lean` files in your assignments. We will use this information in the development of tools for the Lean theorem prover. You can find out more by looking at the [information sheet](InformationSheet.pdf) in this repo. This data will be kept private, besides its use by Kyle Thompson (one of the course TAs), Sorin Lerner, and their immediate collaborators. If at any point you would like to be removed from the study, please notify Kyle Thompson (r7thompson@ucsd.edu). 
