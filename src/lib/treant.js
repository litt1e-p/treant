/*
 * Treant-js
 *
 * (c) 2013 Fran Peručić
 * Treant-js may be freely distributed under the MIT license.
 * For all details and documentation:
 * http://fperucic.github.io/treant-js
 *
 * Treant is an open-source JavaScipt library for visualization of tree diagrams.
 * It implements the node positioning algorithm of John Q. Walker II "Positioning nodes for General Trees".
 *
 * References:
 * Emilio Cortegoso Lobato: ECOTree.js v1.0 (October 26th, 2006)
 *
 * Contributors:
 * Fran Peručić, https://github.com/fperucic
 * Dave Goodchild, https://github.com/dlgoodchild
 */
import $ from 'jquery';
import Raphael from 'raphael';
require('jquery.easing');
require('jquery.mousewheel');
require('perfect-scrollbar');

var UTIL = {
	inheritAttrs: function(me, from) {
		for (var attr in from) {
			if(typeof from[attr] !== 'function') {
				if(me[attr] instanceof Object && from[attr] instanceof Object) {
					this.inheritAttrs(me[attr], from[attr]);
				} else {
					me[attr] = from[attr];
				}
			}
		}
	},
	createMerge: function(obj1, obj2) {
		var newObj = {};
		if(obj1) this.inheritAttrs(newObj, this.cloneObj(obj1));
		if(obj2) this.inheritAttrs(newObj, obj2);
		return newObj;
	},
	cloneObj: function (obj) {
		if (Object(obj) !== obj) {
			return obj;
		}
		var res = new obj.constructor();
		for (var key in obj) if (obj["hasOwnProperty"](key)) {
			res[key] = this.cloneObj(obj[key]);
		}
		return res;
	},
	addEvent: function(el, eventType, handler) {
		if (el.addEventListener) {
			el.addEventListener(eventType, handler, false);
		} else if (el.attachEvent) {
			el.attachEvent('on' + eventType, handler);
		} else {
			el['on' + eventType] = handler;
		}
	},
	hasClass: function(element, my_class) {
		return (" " + element.className + " ").replace(/[\n\t]/g, " ").indexOf(" "+my_class+" ") > -1;
	}
};
var ImageLoader = function() {
	this.loading = [];
};
ImageLoader.prototype = {
	processNode: function(node) {
		var images = node.nodeDOM.getElementsByTagName('img'),
			i =	images.length;
		while(i--) {
			this.create(node, images[i]);
		}
	},
	removeAll: function(img_src) {
		var i = this.loading.length;
		while (i--) {
			if (this.loading[i] === img_src) { this.loading.splice(i,1); }
		}
	},
	create: function (node, image) {
		var self = this,
			source = image.src;
		this.loading.push(source);
		function imgTrigger() {
			self.removeAll(source);
			node.width = node.nodeDOM.offsetWidth;
			node.height = node.nodeDOM.offsetHeight;
		}
		if (image.complete) { return imgTrigger(); }
		UTIL.addEvent(image, 'load', imgTrigger);
		UTIL.addEvent(image, 'error', imgTrigger);
		image.src += "?" + new Date().getTime();
	},
	isNotLoading: function() {
		return this.loading.length === 0;
	}
};
var TreeStore = {
	store: [],
	createTree: function(jsonConfig) {
		this.store.push(new Tree(jsonConfig, this.store.length));
		return this.store[this.store.length - 1];
	},
	get: function (treeId) {
		return this.store[treeId];
	},
	destroy: function(tree_id){
		var tree = this.get(tree_id);
		if (tree) {
			tree._R.remove();
			var draw_area = tree.drawArea;
			while(draw_area.firstChild) {
				draw_area.removeChild(draw_area.firstChild);
			}
			var classes = draw_area.className.split(' '),
				classes_to_stay = [];
			for (var i = 0; i < classes.length; i++) {
				var cls = classes[i];
				if (cls != 'Treant' && cls != 'Treant-loaded') {
					classes_to_stay.push(cls);
				}
			};
			draw_area.style.overflowY = '';
			draw_area.style.overflowX = '';
			draw_area.className = classes_to_stay.join(' ');
			this.store[tree_id] = null;
		}
	}
};
var Tree = function (jsonConfig, treeId) {
	this.id = treeId;
	this.imageLoader = new ImageLoader();
	this.CONFIG = UTIL.createMerge(Tree.CONFIG, jsonConfig.chart);
	this.drawArea = document.getElementById(this.CONFIG.container.substring(1));
	this.drawArea.className += " Treant";
	this.nodeDB = new NodeDB(jsonConfig.nodeStructure, this);
	this.connectionStore = {};
};
Tree.prototype = {
	positionTree: function(callback) {
		var self = this;
		if (this.imageLoader.isNotLoading()) {
			var root = this.root(),
				orient = this.CONFIG.rootOrientation;
			this.resetLevelData();
			this.firstWalk(root, 0);
			this.secondWalk( root, 0, 0, 0 );
			this.positionNodes();
			if (this.CONFIG.animateOnInit) {
				setTimeout(function() { root.toggleCollapse(); }, this.CONFIG.animateOnInitDelay);
			}
			if(!this.loaded) {
				this.drawArea.className += " Treant-loaded"; // nodes are hidden until .loaded class is add
				if (Object.prototype.toString.call(callback) === "[object Function]") { callback(self); }
				this.loaded = true;
			}
		} else {
			setTimeout(function() { self.positionTree(callback); }, 10);
		}
	},
	firstWalk: function(node, level) {
		node.prelim = null; node.modifier = null;
		this.setNeighbors(node, level);
		this.calcLevelDim(node, level);
		var leftSibling = node.leftSibling();
		if(node.childrenCount() === 0 || level == this.CONFIG.maxDepth) {
			if(leftSibling) {
				node.prelim = leftSibling.prelim + leftSibling.size() + this.CONFIG.siblingSeparation;
			} else {
				node.prelim = 0;
			}
		} else {
			for(var i = 0, n = node.childrenCount(); i < n; i++) {
				this.firstWalk(node.childAt(i), level + 1);
			}
			var midPoint = node.childrenCenter() - node.size() / 2;
			if(leftSibling) {
				node.prelim		= leftSibling.prelim + leftSibling.size() + this.CONFIG.siblingSeparation;
				node.modifier	= node.prelim - midPoint;
				this.apportion( node, level );
			} else {
				node.prelim = midPoint;
			}
			if(node.stackParent) {
				node.modifier += this.nodeDB.get( node.stackChildren[0] ).size()/2 + node.connStyle.stackIndent;
			} else if ( node.stackParentId ) { // handle stacked children
				node.prelim = 0;
			}
		}
	},
	apportion: function (node, level) {
		var firstChild = node.firstChild(),
			firstChildLeftNeighbor	= firstChild.leftNeighbor(),
			compareDepth = 1,
			depthToStop	= this.CONFIG.maxDepth - level;
		while( firstChild && firstChildLeftNeighbor && compareDepth <= depthToStop ) {
			var modifierSumRight	= 0,
				modifierSumLeft		= 0,
				leftAncestor		= firstChildLeftNeighbor,
				rightAncestor		= firstChild;
			for(var i = 0; i < compareDepth; i++) {

				leftAncestor		= leftAncestor.parent();
				rightAncestor		= rightAncestor.parent();
				modifierSumLeft		+= leftAncestor.modifier;
				modifierSumRight	+= rightAncestor.modifier;
				if(rightAncestor.stackParent !== undefined) modifierSumRight += rightAncestor.size()/2;
			}
			var totalGap = (firstChildLeftNeighbor.prelim + modifierSumLeft + firstChildLeftNeighbor.size() + this.CONFIG.subTeeSeparation) - (firstChild.prelim + modifierSumRight );
			if(totalGap > 0) {
				var subtreeAux = node,
					numSubtrees = 0;
				while(subtreeAux && subtreeAux.id != leftAncestor.id) {
					subtreeAux = subtreeAux.leftSibling();
					numSubtrees++;
				}
				if(subtreeAux) {
					var subtreeMoveAux = node,
						singleGap = totalGap / numSubtrees;
					while(subtreeMoveAux.id != leftAncestor.id) {
						subtreeMoveAux.prelim	+= totalGap;
						subtreeMoveAux.modifier	+= totalGap;
						totalGap				-= singleGap;
						subtreeMoveAux = subtreeMoveAux.leftSibling();
					}
				}
			}
			compareDepth++;
			if(firstChild.childrenCount() === 0){
				firstChild = node.leftMost(0, compareDepth);
			} else {
				firstChild = firstChild.firstChild();
			}
			if(firstChild) {
				firstChildLeftNeighbor = firstChild.leftNeighbor();
			}
		}
	},
	secondWalk: function( node, level, X, Y) {
		if(level <= this.CONFIG.maxDepth) {
			var xTmp = node.prelim + X,
				yTmp = Y, align = this.CONFIG.nodeAlign,
				orinet = this.CONFIG.rootOrientation,
				levelHeight, nodesizeTmp;
			if (orinet == 'NORTH' || orinet == 'SOUTH') {
				levelHeight = this.levelMaxDim[level].height;
				nodesizeTmp = node.height;
				if (node.pseudo) node.height = levelHeight;
			}
			else if (orinet == 'WEST' || orinet == 'EAST') {
				levelHeight = this.levelMaxDim[level].width;
				nodesizeTmp = node.width;
				if (node.pseudo) node.width = levelHeight;
			}
			node.X = xTmp;
			if (node.pseudo) {
				if (orinet == 'NORTH' || orinet == 'WEST') {
					node.Y = yTmp;
				}
				else if (orinet == 'SOUTH' || orinet == 'EAST') {
					node.Y = (yTmp + (levelHeight - nodesizeTmp));
				}
			} else {
				node.Y = ( align == 'CENTER' ) ? (yTmp + (levelHeight - nodesizeTmp) / 2) :
						( align == 'TOP' )	? (yTmp + (levelHeight - nodesizeTmp)) :
						yTmp;
			}
			if(orinet == 'WEST' || orinet == 'EAST') {
				var swapTmp = node.X;
				node.X = node.Y;
				node.Y = swapTmp;
			}
			if (orinet == 'SOUTH') {
				node.Y = -node.Y - nodesizeTmp;
			}
			else if (orinet == 'EAST') {
				node.X = -node.X - nodesizeTmp;
			}
			if(node.childrenCount() !== 0) {
				if(node.id === 0 && this.CONFIG.hideRootNode) {
					this.secondWalk(node.firstChild(), level + 1, X + node.modifier, Y);
				} else {
					this.secondWalk(node.firstChild(), level + 1, X + node.modifier, Y + levelHeight + this.CONFIG.levelSeparation);
				}
			}
			if(node.rightSibling()) {
				this.secondWalk(node.rightSibling(), level, X, Y);
			}
		}
	},
	positionNodes: function() {
		var self = this,
			treeSize = {
				x: self.nodeDB.getMinMaxCoord('X', null, null),
				y: self.nodeDB.getMinMaxCoord('Y', null, null)
			},
			treeWidth = treeSize.x.max - treeSize.x.min,
			treeHeight = treeSize.y.max - treeSize.y.min,
			treeCenter = {
				x: treeSize.x.max - treeWidth/2,
				y: treeSize.y.max - treeHeight/2
			},
			containerCenter = {
				x: self.drawArea.clientWidth/2,
				y: self.drawArea.clientHeight/2
			},
			deltaX = containerCenter.x - treeCenter.x,
			deltaY = containerCenter.y - treeCenter.y,
			negOffsetX = ((treeSize.x.min + deltaX) <= 0) ? Math.abs(treeSize.x.min) : 0,
			negOffsetY = ((treeSize.y.min + deltaY) <= 0) ? Math.abs(treeSize.y.min) : 0,
			i, len, node;
		this.handleOverflow(treeWidth, treeHeight);
		for(i =0, len = this.nodeDB.db.length; i < len; i++) {
			node = this.nodeDB.get(i);
			if(node.id === 0 && this.CONFIG.hideRootNode) continue;
			node.X += negOffsetX + ((treeWidth < this.drawArea.clientWidth) ? deltaX : this.CONFIG.padding);
			node.Y += negOffsetY + ((treeHeight < this.drawArea.clientHeight) ? deltaY : this.CONFIG.padding);
			var collapsedParent = node.collapsedParent(),
				hidePoint = null;
			if(collapsedParent) {
				hidePoint = collapsedParent.connectorPoint( true );
				node.hide(hidePoint);
			} else if(node.positioned) {
				node.show();
			} else {
				node.nodeDOM.style.left = node.X + 'px';
				node.nodeDOM.style.top = node.Y + 'px';
				node.positioned = true;
			}
			if (node.id !== 0 && !(node.parent().id === 0 && this.CONFIG.hideRootNode)) {
				this.setConnectionToParent(node, hidePoint);
			}
			else if (!this.CONFIG.hideRootNode && node.drawLineThrough) {
				node.drawLineThroughMe();
			}
		}
	},
	handleOverflow: function(treeWidth, treeHeight) {
		var viewWidth = (treeWidth < this.drawArea.clientWidth) ? this.drawArea.clientWidth : treeWidth + this.CONFIG.padding*2,
			viewHeight = (treeHeight < this.drawArea.clientHeight) ? this.drawArea.clientHeight : treeHeight + this.CONFIG.padding*2;
		if(this._R) {
			this._R.setSize(viewWidth, viewHeight);
		} else {
			this._R = Raphael(this.drawArea, viewWidth, viewHeight);
		}
		if(this.CONFIG.scrollbar == 'native') {
			if(this.drawArea.clientWidth < treeWidth) {
				this.drawArea.style.overflowX = "auto";
			}
			if(this.drawArea.clientHeight < treeHeight) {
				this.drawArea.style.overflowY = "auto";
			}
		} else if (this.CONFIG.scrollbar == 'fancy') {
			var jq_drawArea = $(this.drawArea);
			if (jq_drawArea.hasClass('ps-container')) {
				jq_drawArea.find('.Treant').css({
					width: viewWidth,
					height: viewHeight
				});
				jq_drawArea.perfectScrollbar('update');
			} else {
				var mainContiner = jq_drawArea.wrapInner('<div class="Treant"/>'),
					child = mainContiner.find('.Treant');
				child.css({
					width: viewWidth,
					height: viewHeight
				});
				mainContiner.perfectScrollbar();
			}
		}
	},
	setConnectionToParent: function(node, hidePoint) {
		var stacked = node.stackParentId,
			connLine,
			parent = stacked ? this.nodeDB.get(stacked) : node.parent(),
			pathString = hidePoint ? this.getPointPathString(hidePoint):
						this.getPathString(parent, node, stacked);
		if (this.connectionStore[node.id]) {
			connLine = this.connectionStore[node.id];
			this.animatePath(connLine, pathString);
		} else {
			connLine = this._R.path( pathString );
			this.connectionStore[node.id] = connLine;
			if(node.pseudo) { delete parent.connStyle.style['arrow-end']; }
			if(parent.pseudo) { delete parent.connStyle.style['arrow-start']; }
			connLine.attr(parent.connStyle.style);
			if(node.drawLineThrough || node.pseudo) { node.drawLineThroughMe(hidePoint); }
		}
	},
	getPointPathString: function(hp) {
		return ["_M", hp.x, ",", hp.y, 'L', hp.x, ",", hp.y, hp.x, ",", hp.y].join(" ");
	},
	animatePath: function(path, pathString) {
		if (path.hidden && pathString.charAt(0) !== "_") {
			path.show();
			path.hidden = false;
		}
		path.animate({
			path: pathString.charAt(0) === "_" ? pathString.substring(1) : pathString
		}, this.CONFIG.animation.connectorsSpeed,  this.CONFIG.animation.connectorsAnimation,
		function(){
			if(pathString.charAt(0) === "_") {
				path.hide();
				path.hidden = true;
			}
		});
	},
	getPathString: function(from_node, to_node, stacked) {
		var startPoint = from_node.connectorPoint( true ),
			endPoint = to_node.connectorPoint( false ),
			orinet = this.CONFIG.rootOrientation,
			connType = from_node.connStyle.type,
			P1 = {}, P2 = {};
		if (orinet == 'NORTH' || orinet == 'SOUTH') {
			P1.y = P2.y = (startPoint.y + endPoint.y) / 2;
			P1.x = startPoint.x;
			P2.x = endPoint.x;
		} else if (orinet == 'EAST' || orinet == 'WEST') {
			P1.x = P2.x = (startPoint.x + endPoint.x) / 2;
			P1.y = startPoint.y;
			P2.y = endPoint.y;
		}
		var sp = startPoint.x+','+startPoint.y, p1 = P1.x+','+P1.y, p2 = P2.x+','+P2.y, ep = endPoint.x+','+endPoint.y,
			pm = (P1.x + P2.x)/2 +','+ (P1.y + P2.y)/2, pathString, stackPoint;
		if(stacked) {
			stackPoint = (orinet == 'EAST' || orinet == 'WEST') ?
							endPoint.x+','+startPoint.y :
							startPoint.x+','+endPoint.y;
			if( connType == "step" || connType == "straight" ) {
				pathString = ["M", sp, 'L', stackPoint, 'L', ep];
			} else if ( connType == "curve" || connType == "bCurve" ) {
				var helpPoint,
					indent = from_node.connStyle.stackIndent;
				if (orinet == 'NORTH') {
					helpPoint = (endPoint.x - indent)+','+(endPoint.y - indent);
				} else if (orinet == 'SOUTH') {
					helpPoint = (endPoint.x - indent)+','+(endPoint.y + indent);
				} else if (orinet == 'EAST') {
					helpPoint = (endPoint.x + indent) +','+startPoint.y;
				} else if ( orinet == 'WEST') {
					helpPoint = (endPoint.x - indent) +','+startPoint.y;
				}
				pathString = ["M", sp, 'L', helpPoint, 'S', stackPoint, ep];
			}
		} else {
			if( connType == "step" ) {
				pathString = ["M", sp, 'L', p1, 'L', p2, 'L', ep];
			} else if ( connType == "curve" ) {
				pathString = ["M", sp, 'C', p1, p2, ep ];
			} else if ( connType == "bCurve" ) {
				pathString = ["M", sp, 'Q', p1, pm, 'T', ep];
			} else if (connType == "straight" ) {
				pathString = ["M", sp, 'L', sp, ep];
			}
		}
		return pathString.join(" ");
	},
	setNeighbors: function(node, level) {
		node.leftNeighborId = this.lastNodeOnLevel[level];
		if(node.leftNeighborId) node.leftNeighbor().rightNeighborId = node.id;
		this.lastNodeOnLevel[level] = node.id;
	},
	calcLevelDim: function(node, level) {
		if (this.levelMaxDim[level]) {
			if( this.levelMaxDim[level].width < node.width )
				this.levelMaxDim[level].width = node.width;
			if( this.levelMaxDim[level].height < node.height )
				this.levelMaxDim[level].height = node.height;
		} else {
			this.levelMaxDim[level] = { width: node.width, height: node.height };
		}
	},
	resetLevelData: function() {
		this.lastNodeOnLevel = [];
		this.levelMaxDim = [];
	},
	root: function() {
		return this.nodeDB.get( 0 );
	}
};
var NodeDB = function (nodeStructure, tree) {
	this.db	= [];
	var self = this;
	function itterateChildren(node, parentId) {
		var newNode = self.createNode(node, parentId, tree, null);
		if(node.children) {
			newNode.children = [];
			if(node.childrenDropLevel && node.childrenDropLevel > 0) {
				while(node.childrenDropLevel--) {
					var connStyle = UTIL.cloneObj(newNode.connStyle);
					newNode = self.createNode('pseudo', newNode.id, tree, null);
					newNode.connStyle = connStyle;
					newNode.children = [];
				}
			}
			var stack = (node.stackChildren && !self.hasGrandChildren(node)) ? newNode.id : null;
			if (stack !== null) { newNode.stackChildren = []; }
			for (var i = 0, len = node.children.length; i < len ; i++) {
				if (stack !== null) {
					newNode =  self.createNode(node.children[i], newNode.id, tree, stack);
					if((i + 1) < len) newNode.children = [];
				} else {
					itterateChildren(node.children[i], newNode.id);
				}
			}
		}
	}
	if (tree.CONFIG.animateOnInit) nodeStructure.collapsed = true;
	itterateChildren( nodeStructure, -1);
	this.createGeometries(tree);
};
NodeDB.prototype = {
	createGeometries: function(tree) {
		var i = this.db.length, node;
		while(i--) {
			this.get(i).createGeometry(tree);
		}
	},
	get: function (nodeId) {
		return this.db[nodeId];
	},
	createNode: function(nodeStructure, parentId, tree, stackParentId) {
		var node = new TreeNode( nodeStructure, this.db.length, parentId, tree, stackParentId );
		this.db.push( node );
		if( parentId >= 0 ) this.get( parentId ).children.push( node.id );
		if( stackParentId ) {
			this.get( stackParentId ).stackParent = true;
			this.get( stackParentId ).stackChildren.push( node.id );
		}
		return node;
	},
	getMinMaxCoord: function( dim, parent, MinMax ) {
		var parent = parent || this.get(0),
			i = parent.childrenCount(),
			MinMax = MinMax || {
				min: parent[dim],
				max: parent[dim] + ((dim == 'X') ? parent.width : parent.height)
			};
		while(i--) {
			var node = parent.childAt(i),
				maxTest = node[dim] + ((dim == 'X') ? node.width : node.height),
				minTest = node[dim];
			if (maxTest > MinMax.max) {
				MinMax.max = maxTest;
			}
			if (minTest < MinMax.min) {
				MinMax.min = minTest;
			}
			this.getMinMaxCoord(dim, node, MinMax);
		}
		return MinMax;
	},
	hasGrandChildren: function(nodeStructure) {
		var i = nodeStructure.children.length;
		while(i--) {
			if(nodeStructure.children[i].children) return true;
		}
	}
};
var TreeNode = function (nodeStructure, id, parentId, tree, stackParentId) {
	this.id			= id;
	this.parentId	= parentId;
	this.treeId		= tree.id;
	this.prelim		= 0;
	this.modifier	= 0;
	this.stackParentId = stackParentId;
	this.pseudo = nodeStructure === 'pseudo' || nodeStructure['pseudo'];
	this.image = nodeStructure.image;
	this.link = UTIL.createMerge( tree.CONFIG.node.link,  nodeStructure.link);
	this.connStyle = UTIL.createMerge(tree.CONFIG.connectors, nodeStructure.connectors);
	this.drawLineThrough = nodeStructure.drawLineThrough === false ? false : nodeStructure.drawLineThrough || tree.CONFIG.node.drawLineThrough;
	this.collapsable = nodeStructure.collapsable === false ? false : nodeStructure.collapsable || tree.CONFIG.node.collapsable;
	this.collapsed = nodeStructure.collapsed;
	this.text = nodeStructure.text;
	this.nodeInnerHTML	= nodeStructure.innerHTML;
	this.nodeHTMLclass	= (tree.CONFIG.node.HTMLclass ? tree.CONFIG.node.HTMLclass : '') +
							(nodeStructure.HTMLclass ? (' ' + nodeStructure.HTMLclass) : '');
	this.nodeHTMLid		= nodeStructure.HTMLid;
	this.X = 0;
	this.Y = 0
};

TreeNode.prototype = {
	Tree: function() {
		return TreeStore.get(this.treeId);
	},
	dbGet: function(nodeId) {
		return this.Tree().nodeDB.get(nodeId);
	},
	size: function() {
		var orient = this.Tree().CONFIG.rootOrientation;
		if(this.pseudo) return - this.Tree().CONFIG.subTeeSeparation;
		if (orient == 'NORTH' || orient == 'SOUTH')
			return this.width;
		else if (orient == 'WEST' || orient == 'EAST')
			return this.height;
	},
	childrenCount: function () {
		return	(this.collapsed || !this.children) ? 0 : this.children.length;
	},
	childAt: function(i) {
		return this.dbGet( this.children[i] );
	},
	firstChild: function() {
		return this.childAt(0);
	},
	lastChild: function() {
		return this.childAt( this.children.length - 1 );
	},
	parent: function() {
		return this.dbGet( this.parentId );
	},
	leftNeighbor: function() {
		if( this.leftNeighborId ) return this.dbGet( this.leftNeighborId );
	},
	rightNeighbor: function() {
		if( this.rightNeighborId ) return this.dbGet( this.rightNeighborId );
	},
	leftSibling: function () {
		var leftNeighbor = this.leftNeighbor();
		if( leftNeighbor && leftNeighbor.parentId == this.parentId ) return leftNeighbor;
	},
	rightSibling: function () {
		var rightNeighbor = this.rightNeighbor();
		if( rightNeighbor && rightNeighbor.parentId == this.parentId ) return rightNeighbor;
	},
	childrenCenter: function ( tree ) {
		var first = this.firstChild(),
			last = this.lastChild();
		return first.prelim + ((last.prelim - first.prelim) + last.size()) / 2;
	},
	collapsedParent: function() {
		var parent = this.parent();
		if (!parent) return false;
		if (parent.collapsed) return parent;
		return parent.collapsedParent();
	},
	leftMost: function ( level, depth ) {
		if( level >= depth ) return this;
		if( this.childrenCount() === 0 ) return;
		for(var i = 0, n = this.childrenCount(); i < n; i++) {
			var leftmostDescendant = this.childAt(i).leftMost( level + 1, depth );
			if(leftmostDescendant)
				return leftmostDescendant;
		}
	},
	connectorPoint: function(startPoint) {
		var orient = this.Tree().CONFIG.rootOrientation, point = {};
		if(this.stackParentId) {
			if (orient == 'NORTH' || orient == 'SOUTH') { orient = 'WEST'; }
			else if (orient == 'EAST' || orient == 'WEST') { orient = 'NORTH'; }
		}
		if (orient == 'NORTH') {
			point.x = (this.pseudo) ? this.X - this.Tree().CONFIG.subTeeSeparation/2 : this.X + this.width/2;
			point.y = (startPoint) ? this.Y + this.height : this.Y;
		} else if (orient == 'SOUTH') {
			point.x = (this.pseudo) ? this.X - this.Tree().CONFIG.subTeeSeparation/2 : this.X + this.width/2;
			point.y = (startPoint) ? this.Y : this.Y + this.height;
		} else if (orient == 'EAST') {
			point.x = (startPoint) ? this.X : this.X + this.width;
			point.y = (this.pseudo) ? this.Y - this.Tree().CONFIG.subTeeSeparation/2 : this.Y + this.height/2;
		} else if (orient == 'WEST') {
			point.x = (startPoint) ? this.X + this.width : this.X;
			point.y =  (this.pseudo) ? this.Y - this.Tree().CONFIG.subTeeSeparation/2 : this.Y + this.height/2;
		}
		return point;
	},
	pathStringThrough: function() {
		var startPoint = this.connectorPoint(true),
			endPoint = this.connectorPoint(false);
		return ["M", startPoint.x+","+startPoint.y, 'L', endPoint.x+","+endPoint.y].join(" ");
	},
	drawLineThroughMe: function(hidePoint) {
		var pathString = hidePoint ? this.Tree().getPointPathString(hidePoint) : this.pathStringThrough();
		this.lineThroughMe = this.lineThroughMe || this.Tree()._R.path(pathString);
		var line_style = UTIL.cloneObj(this.connStyle.style);
		delete line_style['arrow-start'];
		delete line_style['arrow-end'];
		this.lineThroughMe.attr( line_style );
		if(hidePoint) {
			this.lineThroughMe.hide();
			this.lineThroughMe.hidden = true;
		}
	},

	addSwitchEvent: function(my_switch) {
		var self = this;
		UTIL.addEvent(my_switch, 'click', function(e){
			e.preventDefault();
			self.toggleCollapse();
		});
	},

	toggleCollapse: function() {
		var tree = this.Tree();
		if (! tree.inAnimation) {
			tree.inAnimation = true;
			this.collapsed = !this.collapsed;
			if (this.collapsed) {
				$(this.nodeDOM).addClass('collapsed');
			} else {
				$(this.nodeDOM).removeClass('collapsed');
			}
			tree.positionTree();
			setTimeout(function() {
				tree.inAnimation = false;
			}, tree.CONFIG.animation.nodeSpeed > tree.CONFIG.animation.connectorsSpeed ? tree.CONFIG.animation.nodeSpeed : tree.CONFIG.animation.connectorsSpeed)
		}
	},

	hide: function(collapse_to_point) {
		this.nodeDOM.style.overflow = "hidden";
		var jq_node = $(this.nodeDOM), tree = this.Tree(),
			config = tree.CONFIG,
			new_pos = {
				left: collapse_to_point.x,
				top: collapse_to_point.y
			};
		if (!this.hidden) { new_pos.width = new_pos.height = 0; }
		if(!this.startW || !this.startH) { this.startW = jq_node.outerWidth(); this.startH = jq_node.outerHeight(); }
		if(!this.positioned || this.hidden) {
			this.nodeDOM.style.visibility = 'hidden';
			jq_node.css(new_pos);
			this.positioned = true;
		} else {
			jq_node.animate(new_pos, config.animation.nodeSpeed, config.animation.nodeAnimation,
			function(){
				this.style.visibility = 'hidden';
			});
		}
		if(this.lineThroughMe) {
			var new_path = tree.getPointPathString(collapse_to_point);
			if (this.hidden) {
				this.lineThroughMe.attr({path: new_path});
			} else {
				tree.animatePath(this.lineThroughMe, tree.getPointPathString(collapse_to_point));
			}
		}
		this.hidden = true;
	},

	show: function() {
		this.nodeDOM.style.visibility = 'visible';
		var new_pos = {
			left: this.X,
			top: this.Y
		},
		tree = this.Tree(),  config = tree.CONFIG;
		if(this.hidden) {
			new_pos.width = this.startW;
			new_pos.height = this.startH;
		}
		$(this.nodeDOM).animate(
			new_pos,
			config.animation.nodeSpeed, config.animation.nodeAnimation,
			function() {
				this.style.overflow = "";
			}
		);
		if(this.lineThroughMe) {
			tree.animatePath(this.lineThroughMe, this.pathStringThrough());
		}
		this.hidden = false;
	}
};

TreeNode.prototype.createGeometry = function(tree) {
	if (this.id === 0 && tree.CONFIG.hideRootNode) {
		this.width = 0; this.height = 0;
		return;
	}
	var drawArea = tree.drawArea,
		image, i,
	node = this.link.href ? document.createElement('a') : document.createElement('div');
	node.className = (!this.pseudo) ? TreeNode.CONFIG.nodeHTMLclass : 'pseudo';
	if(this.nodeHTMLclass && !this.pseudo) node.className += ' ' + this.nodeHTMLclass;
	if(this.nodeHTMLid) node.id = this.nodeHTMLid;
	if(this.link.href) {
		node.href = this.link.href;
		node.target = this.link.target;
	}
	if (!this.pseudo) {
		if (!this.nodeInnerHTML) {
			if(this.image) {
				image = document.createElement('img');
				image.src = this.image;
				node.appendChild(image);
			}
			if(this.text) {
				for(var key in this.text) {
					if(TreeNode.CONFIG.textClass[key]) {
						var text = document.createElement(this.text[key].href ? 'a' : 'p');
						if (this.text[key].href) {
							text.href = this.text[key].href;
							if (this.text[key].target) { text.target = this.text[key].target; }
						}
						text.className = TreeNode.CONFIG.textClass[key];
						text.appendChild(document.createTextNode(
							this.text[key].val ? this.text[key].val :
								this.text[key] instanceof Object ? "'val' param missing!" : this.text[key]
							)
						);
						node.appendChild(text);
					}
				}
			}
		} else {
			if (this.nodeInnerHTML.charAt(0) === "#") {
				var elem = document.getElementById(this.nodeInnerHTML.substring(1));
				if (elem) {
					node = elem.cloneNode(true);
					node.id += "-clone";
					node.className += " node";
				} else {
					node.innerHTML = "<b> Wrong ID selector </b>";
				}
			} else {
				node.innerHTML = this.nodeInnerHTML;
			}
		}
		if (this.collapsed || (this.collapsable && this.childrenCount() && !this.stackParentId)) {
			var my_switch = document.createElement('a');
			my_switch.className = "collapse-switch";
			node.appendChild(my_switch);
			this.addSwitchEvent(my_switch);
			if (this.collapsed) { node.className += " collapsed"; }
		}
	}
	drawArea.appendChild(node);
	this.width = node.offsetWidth;
	this.height = node.offsetHeight;
	this.nodeDOM = node;
	tree.imageLoader.processNode(this);
};

Tree.CONFIG = {
	maxDepth: 100,
	rootOrientation: 'NORTH', // NORTH || EAST || WEST || SOUTH
	nodeAlign: 'CENTER', // CENTER || TOP || BOTTOM
	levelSeparation: 30,
	siblingSeparation: 30,
	subTeeSeparation: 30,
	hideRootNode: false,
	animateOnInit: false,
	animateOnInitDelay: 500,
	padding: 15,
	scrollbar: 'native', // "native" || "fancy" || "None" (PS: "fancy" requires jquery and perfect-scrollbar)
	connectors: {
		type: 'curve', // 'curve' || 'step' || 'straight' || 'bCurve'
		style: {
			stroke: 'black'
		},
		stackIndent: 15
	},
	node: { // each node inherits this, it can all be overrifen in node config
		// HTMLclass: 'node',
		// drawLineThrough: false,
		// collapsable: false,
		link: {
			target: '_self'
		}
	},
	animation: { // each node inherits this, it can all be overrifen in node config
		nodeSpeed: 450,
		nodeAnimation: 'linear',
		connectorsSpeed: 450,
		connectorsAnimation: 'linear'
	}
};

TreeNode.CONFIG = {
	nodeHTMLclass: 'node',
	textClass: {
		name:	'node-name',
		title:	'node-title',
		desc:	'node-desc',
		contact: 'node-contact'
	}
};

var JSONconfig = {
	make: function( configArray ) {
		var i = configArray.length, node;
		this.jsonStructure = {
			chart: null,
			nodeStructure: null
		};
		while(i--) {
			node = configArray[i];
			if (node.hasOwnProperty('container')) {
				this.jsonStructure.chart = node;
				continue;
			}
			if (!node.hasOwnProperty('parent') && ! node.hasOwnProperty('container')) {
				this.jsonStructure.nodeStructure = node;
				node.myID = this.getID();
			}
		}
		this.findChildren(configArray);
		return this.jsonStructure;
	},
	findChildren: function(nodes) {
		var parents = [0];
		while(parents.length) {
			var parentId = parents.pop(),
				parent = this.findNode(this.jsonStructure.nodeStructure, parentId),
				i = 0, len = nodes.length,
				children = [];
			for(;i<len;i++) {
				var node = nodes[i];
				if(node.parent && (node.parent.myID == parentId)) {
					node.myID = this.getID();
					delete node.parent;
					children.push(node);
					parents.push(node.myID);
				}
			}
			if (children.length) {
				parent.children = children;
			}
		}
	},
	findNode: function(node, nodeId) {
		var childrenLen, found;
		if (node.myID === nodeId) {
			return node;
		} else if (node.children) {
			childrenLen = node.children.length;
			while(childrenLen--) {
				found = this.findNode(node.children[childrenLen], nodeId);
				if(found) {
					return found;
				}
			}
		}
	},
	getID: (function() {
		var i = 0;
		return function() {
			return i++;
		};
	})()
};
var Treant = function(jsonConfig, callback) {
	if (jsonConfig instanceof Array) {
		jsonConfig = JSONconfig.make(jsonConfig);
	}
	var newTree = TreeStore.createTree(jsonConfig);
	newTree.positionTree(callback);
	this.tree_id = newTree.id;
};
Treant.prototype.destroy = function() {
	TreeStore.destroy(this.tree_id);
};
export default Treant;
