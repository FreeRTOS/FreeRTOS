
	var openImg   = new Image();
	openImg.src   = "imgs/IMG_openBranch.gif";
		
	var closeImg  = new Image();
	closeImg.src  = "imgs/IMG_closeBranch.gif";
		
	function showBranch(branchId) {
		
		var branchObj = document.getElementById(branchId).style;
			
		if(branchObj.display== "block")
			   branchObj.display = "none";
		else   
		   branchObj.display = "block";
	}
		
	function swapBranchImg(branchImgId) {
		
		branchImg = document.getElementById(branchImgId);
		
		if(branchImg.src.indexOf('IMG_closeBranch.gif') > -1)
			branchImg.src = openImg.src;
		else   
		    branchImg.src = closeImg.src;
	}
	